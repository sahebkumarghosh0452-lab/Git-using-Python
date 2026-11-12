import argparse,collections, difflib,enum, hashlib,operator,os,stat
import struct,sys,time,urllib.request,zlib

IndexEntry = collections.namedtuple('indexEntry',['ctime_s','ctime_n','mtime_s','mtime_n','dev','ino','mode','uid','gid','size','sha1','flags','path',])

'''
ctime_s, ctime_n: Creation/change time (seconds and nanoseconds fraction).

mtime_s, mtime_n: Last modification time (seconds and nanoseconds fraction).

dev, ino: Device and inode identifiers on the filesystem.

mode: File permissions and type (e.g., regular file, executable, symlink).

uid, gid: User ID and Group ID of the file owner.

size: File size in bytes.

sha1: 20-byte SHA-1 hash of the staged blob object in .git/objects.

flags: 16-bit field encoding stage numbers (merge conflicts) and path length metadata.

path: Relative file path as a string.
'''


class ObjectType(enum.Enum):
    commit = 1
    tree = 2
    blob = 3
    
def read_file(path):
    with open(path,'rb') as f :  # opens the file in binary read mode and "with" is used as closing expression if errors or end of reading reached
        return f.read()

def write_file(path,data):
    with open(path,'wb') as f :
        f.write(data)

def init(repo):
    os.mkdir(repo)
    os.mkdir(os.path.join(repo,'.git'))
    for name in ['objects','refs','refs/heads']:
        os.mkdir(os.path.join(repo,'.git',name)),
    #Creates essential subdirectories for storing hashed objects (blobs, trees, commits) and branch reference pointers.
    write_file(os.path.join(repo,'.git','HEAD'),b'ref: refs/heads/master') # initialized head pointer to the main branch
    print('initialized empty repository:{}'.format(repo))
    
def hash_obj(data,obj_type,write=True):
    header = '{} {}'.format(obj_type,len(data)).encode()
    full_data = header + b'\x00' + data
    sha1 = hashlib.sha1(full_data).hexdigest() #computes the 40-character hexadecimal SHA-1 hash of the assembled data, which serves as the object's unique ID.
    if write:
        path = os.path.join('.git','objects',sha1[:2],sha1[2:]) # Splits the hash into a 2-character directory prefix and a 38-character filename to avoid cluttering a single folder with thousands of files.
        if not os.path.exists(path):
            os.makedirs(os.path.dirname(path),exist_ok=True)
            write_file(path,zlib.compress(full_data))
    return sha1

def find_object(sha1_prefix):
    if len(sha1_prefix) < 2:  # minimum needed to determine the two-character subdirectory name.
        raise ValueError('hash prefix must be 2 or more character')
    
    obj_dir = os.path.join('.git','objects',sha1_prefix[:2]) # locates the folder based on the first two hex characters
    
    rest = sha1_prefix[2:] # extracts the remaining characters to match against.
    
    objects = [name for name in os.listdir(obj_dir) if name.startswith(rest)] # scans the target directory and collects every filename starting with the remaining prefix.
    
    # ERROR HANDLING 
    if not objects :
        raise ValueError('object {!r} not found'.format(sha1_prefix))
    if len(objects) >= 2 :
        raise ValueError('multiple objects ({}) with prefix {!r}'.format(len(objects),sha1_prefix))
    
    return os.path.join(obj_dir,objects[0]) #absolute/relative path to the single matching object file.

def read_object(sha1_prefix):
    path = find_object(sha1_prefix) # uses the prefix lookup helper to locate the target object file inside .git/objects/.
    full_data = zlib.decompress(read_file(path)) #decompressing 
    nul_index = full_data.index(b'\x00') #finds the null-byte delimiter separating the header from the payload.
    header = full_data[:nul_index] # isolates the header bytes.
    obj_type, size_str = header.decode().split() #parses object and size str
    size = int(size_str)
    data = full_data[nul_index+1:] # slices out the actual content immediately following the null byte.
    assert size == len(data),'expected size {},got {} bytes'.format(size,len(data)) # verifies data integrity by ensuring the decoded payload length matches the byte size declared in the header.
    return (obj_type,data) # tuple of obj and raw byte payload.

def cat_file(mode,sha1_prefix):
    obj_type,data = read_object(sha1_prefix)
    if mode in ['commit','tree','blob']:
        if obj_type != mode :
            raise ValueError('expected object type {},got {}'.format(mode,obj_type))
        sys.stdout.buffer.write(data)
    elif mode == 'size' :  print(len(data))
    elif mode == 'type' : print(obj_type)
    elif mode == 'pretty' : 
        if obj_type in ['commit','bolb']:
            sys.stdout.buffer.write(data)
        elif obj_type == 'tree' :
            for mode,path,sha1 in read_tree(data = data):
                type_str = 'tree' if stat.S_ISDIR(mode) else 'blob'
                print('{:06o} {} {}\t{}'.format(mode,type_str,sha1,path))
        else :
            assert False,'unhandled object type {!r}'.format(obj_type)
    else :
        raise ValueError('unexpected mode {!r}'.format(mode))
    
def read_index():
    try:
        data = read_file(os.path.join('.git','index'))
    except FileNotFoundError:
        return []
    digest = hashlib.sha1(data[:-20]).digest()   # last 20 bytes of the index file (data[-20:]) are the expected SHA-1 hash of everything preceding it (data[:-20])
    assert digest == data[-20:], 'invalid index checksum'
    
    signature,version,num_entries = struct.unpack('!4sLL',data[:12])
    '''
    !4sLL decodes the 12-byte header using network (big-endian) byte order:

        4s: 4-byte signature; Git always uses b'DIRC' ("Directory Cache").

        L: 4-byte unsigned integer for the format version (this function targets version 2).

        L: 4-byte unsigned integer indicating the total count of staged entries.
    '''
    assert signature == b'DIRC','invalid index signature {}'.format(signature)
    assert version == 2 , 'unknown index version {}'.format(version)
    
    
    entry_data = data[12:-20]  # Slices out the body between the 12-byte header and the 20-byte checksum.
    entries = []
    i = 0 
    
    
    '''
    Each entry begins with a fixed 62-byte block unpacked by !LLLLLLLLLL20sH:
        Ten 4-byte unsigned integers (LLLLLLLLLL = 40 bytes) for timestamps, device, inode, mode, UID, GID, and size.
        20s (20 bytes) for the raw SHA-1 hash.H (2-byte unsigned short) for flags.
        Total = $40 + 20 + 2 = 62$ bytes.
    '''
    while i+62 < len(entry_data):
        fields_end = i + 62
        fields = struct.unpack('!LLLLLLLLLL20sH',entry_data[i:fields_end])
        
        path_end = entry_data.index(b'\x00',fields_end)#path follows the 62-byte header as a null-terminated (\x00) string.
        
        path = entry_data[fields_end:path_end]
        
        entry = IndexEntry(*(fields+(path.decode(),))) # Finds the null byte, decodes the path to a Python string, merges it with the unpacked stat fields, and instantiates an IndexEntry
        
        '''
        Git index entries are padded with null bytes so each entry's total size is a multiple of 8 bytes.

        Even if the path naturally aligns, Git requires at least 1 null byte to terminate the string.

        The arithmetic ((62 + len(path) + 8) // 8) * 8 rounds up to the next multiple of 8, effectively advancing the index pointer i past the path and its trailing zero padding.
        '''
        entries.append(entry)
        entry_len = ((62+len(path)+8)//8)*8 
        i += entry_len
        
    # Verifies that the count of parsed entries matches the num_entries declared in the file header, then returns the list of IndexEntry objects.
    assert len(entries) == num_entries
    return entries

def ls_files(details = False):
    for entry in read_index():
        if details:
            stage = (entry.flags >> 12) & 3
            print('{:6o} {} {:}\t{}'.format(entry.mode,entry.sha1.hex(),stage,entry.path))
        else :
            print(entry.path)
            
def get_status():
    paths = set()
    for root,dirs,files in os.walk('.'):
        dirs[:] = [d for d in dirs if d != '.git']
        for file in files :
            path = os.path.join(root,file)
            path = path.replace('\\','/')
            if path.startswith('./'):
                path = path[2:]
            path.add(path)
    entries_by_path = {e.path:e for e in read_index()}
    entry_paths = set(entries_by_path)
    changed = {p for p in (paths & entry_paths)
               if hash_obj(read_file(p),'blob',write = False) != entries_by_path[p].sha1.hex()}
    new = paths - entry_paths
    deleted = entry_paths - paths
    return (sorted(changed),sorted(new),sorted(deleted))

def status() :
    changed,new,deleted = get_status()
    if changed:
         print('changed files:')
         for path in changed :
             print('   ',path)
    if new :
        print('new files:')
        for path in new :
            print('   ',path)
    if deleted:
        print('deleted files:')
        for path in deleted:
            print('   ',path)

def diff():
    changed, _,_ = get_status()
    entries_by_path = {e.path:e for e in read_index()}
    for i, path in enumerate(changed):
        sha1 = entries_by_path[path].sha1.hex()
        obj_type,data = read_object(sha1)
        assert obj_type == 'blob'
        index_lines = data.decode().splitlines() #Decodes the staged blob bytes into a string and splits it into a list of lines representing the staged version of the file.
        working_lines = read_file(path).decode().splitlines()#Reads the current file directly from disk, decodes the raw bytes, and splits it into a list of lines representing the working copy.
        diff_lines = difflib.unified_diff(
            index_lines,working_lines,'{} (index)'.format(path),'{} (working copy)'.format(path),lineterm='')
        for line in diff_lines :
            print(line)
        if i < len(changed) - 1 :
            print('-' * 70)

def write_index(entries):
    packed_entries = []
    '''!: Network byte order (big-endian).

        Format string breakdown (62 bytes total):

            10L: Ten 32-bit unsigned integers (4 bytes each = 40 bytes) representing file metadata:

            ctime_s, ctime_n: Last metadata change time (seconds and nanosecond fractions).

            mtime_s, mtime_n: Last file modification time (seconds and nanosecond fractions).

            dev, ino: Device and inode numbers on the filesystem.

            mode: File permissions and object type (e.g., standard file vs. executable vs. symlink).

            uid, gid: User and group IDs of the owner.

            size: Truncated on-disk file size.

        20s: 20 raw bytes for the binary SHA-1 object ID representing the blob contents.

        H: A 16-bit unsigned integer (2 bytes) storing Git staging flags (including the 12-bit path length mask, assume-unchanged flag, stage level, etc.).'''
    for entry in entries :
        entry_head = struct.pack('!LLLLLLLLLL20sH',entry.ctime_s,entry.ctime_n, entry.mtime_s,entry.mtime_n,entry.dev,entry.ino,entry.mode,entry.uid,entry.gid,entry.size,entry.sha1,entry.flags)
        
        path = entry.path.encode()
        length = ((62 + len(path) + 8)//8)*8
        packed_entry = entry_head + path + b'\x00' * (length - 62 - len(path)) 
        # b'\x00' - for null padding to make it multiple of 8 bytes
        
        packed_entries.append(packed_entry)

    '''12-byte header:

        b'DIRC': 4-byte signature standing for "Directory Cache".

        2: 32-bit integer indicating the format version (Version 2).

        len(entries): 32-bit integer representing the total count of index entries.'''
    header = struct.pack('!4sLL',b'DIRC',2,len(entries))
    
    all_data = header + b''.join(packed_entries)
    digest = hashlib.sha1(all_data).digest()
    write_file(os.path.join('.git','index'),all_data+digest)

def add(paths):
    # Add files to the git index
    paths = [p.replace('\\','/') for p in paths]
    all_entries = read_index()
    entries = [e for e in all_entries if e.path not in paths]
    for path in paths:
        sha1 = hash_obj(read_file(path),'blob')
        st = os.stat(path)
        flags = len(path.encode())
        assert flags < (1 << 12) #Ensure the path byte length fits within 12 bits (max 4095 bytes) per Git's index format spec
        entry = IndexEntry(
            int(st.st_ctime),0,int(st.st_mtime),0,st.st_dev,st.st_ino,st.st_mode,st.st_vid,st.st_gid,st.st_size,bytes.fromhex(sha1),flags,path
        )
        entries.append(entry)
    entries.sort(key=operator.attrgetter('path')) ## Sort all entries lexicographically by path (required by Git's binary index specification)
    write_index(entries)
    
def write_tree():
    tree_entries = []
    for entry in read_index():
        assert '/' not in entry.path,'currently only supports a single ,top level directory'
        
        mode_path = '{:o} {}'.format(entry.mode,entry.path).encode() # Format the file permissions in octal followed by a space and the filename, then encode to bytes
        
        tree_entry = mode_path + b'\x00' + entry.sha1 # Construct the binary Git tree entry: "<octal_mode> <filename>\0<20-byte_raw_sha1>"
        
        tree_entries.append(tree_entry)
    return hash_obj(b''.join(tree_entries),'tree') # Concatenate all binary entries together

def get_local_master_hash(): 
    #Get current commit hash of local master branch
    master_path = os.path.join('.git','refs','heads','master')
    try:
        return read_file(master_path).decode().strip()
    except FileNotFoundError:
        return None

def commit(message,author = None):
    # Commmit the files with msg and return hash of commit
    tree = write_tree()
    parent = get_local_master_hash()
    if author is None:
        author = f'{os.environ['GIT_AUTHOR_NAME']} <{os.environ['GIT_AUTHOR_EMAIL']}>'
    timestamp = int(time.mktime(time.localtime()))
    utc_offset = -time.timezone
    author_time = f'{timestamp}{'+' if utc_offset>0 else '-'}{abs(utc_offset)//3600:02}{(abs(utc_offset)//60)%60:02}'
    lines = ['tree' + tree]
    if parent:
        lines.append('parent'+parent)
    lines.append(f'author {author} {author_time}')
    lines.append(f'committer {author} {author_time}')
    lines.append('')
    lines.append(message)
    lines.append('')
    data = '\n'.join(lines).encode()
    sha1 = hash_obj(data,'commit')
    master_path = os.path.join('.git','refs','heads','master')
    write_file(master_path,(sha1+'\n').encode())
    print(f'committed to master : {sha1:7}')
    return sha1

def extract_lines(data):
    #Extract lines from server data
    lines = []
    i = 0 
    while i < len(data): # Iter through the byte stream
        line_len = int(data[i:i+4], 16) #4-character hex prefix specifying the total packet length
        
        if line_len == 0: # A len of 0 is a Git 'flush-pkt' delimiter : separate protocol sectns
            lines.append(b'')  #empty line for the flush pkt
            i += 4             # Adv piter past the 4-byte '0000' header
        else:
            line = data[i+4:i+line_len]
            lines.append(line)
            i += line_len # Adv pter to the st of the next pkt-line
    return lines


def build_lines_data(lines):
    #Building byte string from given 
    result = []
    for line in lines:
        result.append(f'{len(line)+5:04x}'.encode())
        result.append(line)
        result.append(b'\n')
    result.append(b'0000')
    return b''.join(result)

def http_req(url,username,pasword,data = None):
    """Make an authenticated HTTP request to given URL (GET by default, POST
        if "data" is not None).
    """
    password_manager = urllib.request.HTTPPasswordMgrWithDefaultRealm()
    password_manager.add_password(None,url,username,pasword)
    auth_handler = urllib.request.AbstractBasicAuthHandler(password_manager)
    opener = urllib.request.build_opener(auth_handler)
    f = opener.open(url,data=data)
    return f.read()

def get_remote_master_hash(git_url,username,password):
    # get commit hash of remote branch
    url = f'{git_url}/info/refs?service=git-receive-pack'
    response = http_req(url,username,password)
    lines = extract_lines(response)
    assert lines[0] == b'# service=git-receive-pack\n' #1st packet is the std Smart HTTP service announcement
    assert lines[1] == b'' #2nd pkt is an empty flush-pkt separating the header from refs
    if lines[2][:40] == b'0'*40: #repo is completely empty, the server advertises 40 0s
        return None
    
    master_sha1,master_ref = lines[2].split(b'\x00')[0].split() # Strip off the null-byte (\x00) and server capabilities suffix, then split into "<sha1> <ref_name>"
    
    assert master_ref == b'refs/heads/master'
    assert len(master_sha1) == 40 # 40-char SHA-1 hex str
    return master_sha1.decode() #ASCII bytes into a std Py str

def read_tree(sha1=None, data=None):
    """Read tree object with given SHA-1 (hex string) or data, and return list
    of (mode, path, sha1) tuples.
    """
    if sha1 is not None:
        obj_type, data = read_object(sha1)
        assert obj_type == 'tree'
    elif data is None:
        raise TypeError('must specify "sha1" or "data"')
    i = 0
    entries = []
    for _ in range(1000):
        end = data.find(b'\x00', i) # Find the null byte (\x00) separating "<mode> <filename>" from the 20-byte SHA-1
        if end == -1:
            break
        mode_str, path = data[i:end].decode().split() #ASCII header before the null byte & split into octal mode and filename
        mode = int(mode_str, 8) #oct -> int
        digest = data[end + 1:end + 21]
        entries.append((mode, path, digest.hex()))
        i = end + 1 + 20 # 1 = null B & 20 = sha-1 hex
    return entries

def find_tree_objects(tree_sha1):
    """Return set of SHA-1 hashes of all objects in this tree,
    including the hash of the tree itself.
    """
    objects = {tree_sha1}
    for mode, path, sha1 in read_tree(sha1=tree_sha1):
        if stat.S_ISDIR(mode):
            objects.update(find_tree_objects(sha1)) #Recure & collect all tree & blob SHA-1s inside the subdirectory & merge into our set
        else:
            objects.add(sha1) # Otherwise its a reg file (blob) or symlink; add its SHA-1 hash directly to the set
    return objects

def find_commit_objects(commit_sha1,visited =None):
    """Return set of SHA-1 hashes of all obj in this commit,
    its tree,parents,& the hash of the commit itself.
    """
    # Track visited commits to avoid redundant work on merge diamonds & prevent infi loops
    if visited is None:
        visited = set()
    if commit_sha1 in visited:
        return set()
    objects = {commit_sha1}
    obj_type, commit = read_object(commit_sha1) # Fetch & decomp the Git obj from .git/objects,verify its a 'commit'
    assert obj_type == 'commit'
    lines = commit.decode().splitlines() #raw commit bytes into UTF-8 text & split into individual lines
    tree = next(l[5:45] for l in lines if l.startswith('tree '))
    objects.update(find_tree_objects(tree)) # Recursively collect the root tree hash, all nested subtrees, & all file blobs
    parents = (l[7:47] for l in lines if l.startswith('parent ')) # Find all 'parent <40-char-sha1>' header lines (0 = root commit, 1 = normal, 2+ = merges)
    for parent in parents: #trav each parent commit's history & merge its objs into our set
        objects.update(find_commit_objects(parent,visited))
    return objects

def find_missing_objects(local_sha1, remote_sha1):
    '''Return set of SHA-1 hashes of objects in local commit that are missing at the remote (based on the given remote commit hash).'''
    local_objects = find_commit_objects(local_sha1) # Collect the full set of commit, tree, and blob SHA-1s reachable from our local commit
    if remote_sha1 is None: #empty repo : up everything
        return local_objects
    remote_objects = find_commit_objects(remote_sha1)
    return local_objects - remote_objects #only objs reachable locally that the remote does not yet have

def encode_pack_object(obj):
    """Encode a single obj for a pack file & return bytes (var-len header followed by compressed data bytes).
    """
    obj_type, data = read_object(obj)
    type_num = ObjectType[obj_type].value # Convt the type name into Git's numeric packfile type code (1=commit, 2=tree,3=blob,4=tag)
    size = len(data)
    byte = (type_num << 4) | (size & 0x0f) # Pack the 3-bit obj type (bits 6–4) & the lowest 4 bits of the size (bits 3–0) into the first byte
    size >>= 4 # avoid up(^) 4
    header = []
    while size:
        header.append(byte | 0x80) #emit the curr byte with its MSB (0x80) set as a continuatn flag
        byte = size & 0x7f #7 least-signif bits of the remaining size
        size >>= 7
    header.append(byte)
    return bytes(header) + zlib.compress(data)

    ''' 7     6   5   4     3   2   1   0
        +---+---------------+---------------+
        | C |   Object Type |  Size (low 4) |
        +---+---------------+---------------+
        │         │               └── Lowest 4 bits uncompressed size (size & 0x0f)
        │         └────────────────── 3-bit ObjectType enum value (type_num << 4)
        └──────────────────────────── Continuation bit: 1 if more size bytes follow, 0 if done'''
def create_pack(objects):
    """Create pack file containing all objects in given given set of SHA-1 hashes, return data bytes of full pack file.
    """
    header = struct.pack('!4sLL', b'PACK', 2, len(objects))
    '''
    # - 4-byte signature: b'PACK'
    # - 4-byte unsigned int (L): packfile version number (2)
    # - 4-byte unsigned int (L): total count of objects packed inside
    '''
    body = b''.join(encode_pack_object(o) for o in sorted(objects)) #Sort obj SHA-1s for deterministic output, encode each into (varint header + zlib data), & concat all encoded objs into a single contiguous byte stream
    contents = header + body
    sha1 = hashlib.sha1(contents).digest()
    data = contents + sha1
    return data

def push(git_url, username=None, password=None):
    """Push master branch to given git repo URL."""
    if username is None:
        username = os.environ['GIT_USERNAME']
    if password is None:
        password = os.environ['GIT_PASSWORD']
    remote_sha1 = get_remote_master_hash(git_url, username, password)
    local_sha1 = get_local_master_hash()
    missing = find_missing_objects(local_sha1, remote_sha1)
    print(f'updating remote master from {remote_sha1 or 'no commits'} to {local_sha1} ({len(missing)} object{'' if len(missing) == 1 else 's'})')
    lines = [f'{remote_sha1 or ('0'*40)} {local_sha1} refs/heads/master\x00 report-status'.encode()]
    data = build_lines_data(lines) + create_pack(missing)
    url = git_url + '/git-receive-pack'
    response = http_req(url, username, password, data=data)
    lines = extract_lines(response)
    assert len(lines) >= 2,f'expected at least 2 lines, got {len(lines)}'
    assert lines[0] == b'unpack ok\n', f"expected line 1 b'unpack ok', got: {lines[0]}"
    assert lines[1] == b'ok refs/heads/master\n', f"expected line 2 b'ok refs/heads/master\n', got: {lines[1]}"
    return (remote_sha1, missing)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    sub_parsers = parser.add_subparsers(dest='command', metavar='command')
    sub_parsers.required = True

    sub_parser = sub_parsers.add_parser('add',help='add file(s) to index')
    sub_parser.add_argument('paths', nargs='+', metavar='path',help='path(s) of files to add')

    sub_parser = sub_parsers.add_parser('cat-file',
            help='display contents of object')
    valid_modes = ['commit', 'tree', 'blob', 'size', 'type', 'pretty']
    sub_parser.add_argument('mode', choices=valid_modes,
            help='object type (commit, tree, blob) or display mode (size,''type, pretty)')
    sub_parser.add_argument('hash_prefix',
            help='SHA-1 hash (or hash prefix) of object to display')

    sub_parser = sub_parsers.add_parser('commit',
            help='commit current state of index to master branch')
    sub_parser.add_argument('-a', '--author',
            help='commit author in format "A U Thor <author@example.com>" (uses GIT_AUTHOR_NAME and GIT_AUTHOR_EMAIL environment variables by default)')
    sub_parser.add_argument('-m', '--message', required=True,
            help='text of commit message')

    sub_parser = sub_parsers.add_parser('diff',
            help='show diff of files changed (between index and working''copy)')

    sub_parser = sub_parsers.add_parser('hash-object',
            help='hash contents of given path (and optionally write to object store)')
    sub_parser.add_argument('path',
            help='path of file to hash')
    sub_parser.add_argument('-t', choices=['commit', 'tree', 'blob'],default='blob', dest='type',
            help='type of object (default %(default)r)')
    sub_parser.add_argument('-w', action='store_true',      dest='write',
            help='write object to object store (as well as printing hash)')

    sub_parser = sub_parsers.add_parser('init',
            help='initialize a new repo')
    sub_parser.add_argument('repo',
            help='directory name for new repo')

    sub_parser = sub_parsers.add_parser('ls-files',
            help='list files in index')
    sub_parser.add_argument('-s', '--stage', action='store_true',
            help='show object details (mode, hash, and stage number) in addition to path')

    sub_parser = sub_parsers.add_parser('push',
            help='push master branch to given git server URL')
    sub_parser.add_argument('git_url',
            help='URL of git repo, eg: https://github.com/benhoyt/pygit.git')
    sub_parser.add_argument('-p', '--password',
            help='password to use for authentication (uses GIT_PASSWORD environment variable by default)')
    sub_parser.add_argument('-u', '--username',
            help='username to use for authentication (uses GIT_USERNAME environment variable by default)')

    sub_parser = sub_parsers.add_parser('status',
            help='show status of working copy')

    args = parser.parse_args()
    if args.command == 'add': add(args.paths)
    elif args.command == 'cat-file':
        try:
            cat_file(args.mode, args.hash_prefix)
        except ValueError as error:
            print(error, file=sys.stderr)
            sys.exit(1)
    elif args.command == 'commit': commit(args.message, author=args.author)
    elif args.command == 'diff': diff()
    elif args.command == 'hash-object':
        sha1 = hash_obj(read_file(args.path), args.type, write=args.write)
        print(sha1)
    elif args.command == 'init': init(args.repo)
    elif args.command == 'ls-files': ls_files(details=args.stage)
    elif args.command == 'push':
        push(args.git_url, username=args.username, password=args.password)
    elif args.command == 'status': status()
    else: assert False, f'unexpected command {args.command!r}'