
module tour/addressBook3

open util/ordering [Book] // Bookに順序付けを行う。

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	names: set Name,
	addr: names -> some Target 
	}
	{ 
	no n: Name | n in n.^(addr)
	all a: Alias | lone a.addr   
	}

//-----------------------------------------------------------------//

pred init (b: Book) {
	no b.addr
	}
pred add (b, b': Book, n: Name, t: Target) {
	t in Addr or some lookup[b,t] // 事前条件を追加。
	b'.addr = b.addr + n -> t
	}
pred del (b, b': Book, n: Name, t: Target) { 
	no b.addr.n or some n.(b.addr) - t // このnへのaddrが無い or nにはt以外のaddrが存在する。
	b'.addr = b.addr - n -> t
	}
fun lookup (b: Book, n: Name) : set Addr { 
	n.^(b.addr) & Addr 
	}
// orderingモジュールにはfirst,next,lastでアクセスする。
fact traces {
	init [first]
	all b: Book - last | let b' = next[b] |
	  some n: Name, t: Target | add[b,b',n,t] or del[b,b',n,t]
	}

private pred show1 (b: Book) {some b.addr}
private pred show2 (b: Book) {some Alias.(b.addr) } 
private pred show3 {}
run show1 for 5
//run show3 for 5

//-----------------------------------------------------------------//

assert lookupYields { 
	all b:Book, n:b.names | some lookup[b,n]
	}
check lookupYields for 6 but 10 Book //6

assert delUndoesAdd2 { 
	all b,b',b'': Book, n: Name, t:Target |
		no n.(b.addr) and add [b, b', n, t] and del [b', b'', n, t] 
		implies b.addr = b''.addr
	}
check delUndoesAdd2 for 10 but 3 Book 

assert addIdempotent { 
	all b,b',b'': Book, n: Name, t:Target |
		add[b, b', n, t] and add[b', b'', n, t] implies b'.addr = b''.addr
	}
check addIdempotent for 3 

assert addLocal { 
	all b,b': Book, n,n': Name, t:Target |
		add[b,b',n,t] and n != n' implies lookup[b,n'] = lookup[b',n']
	}
//check addLocal for 3 but 2 Book // 反例が出てしまう。ただし仕様的にはこれで良い。


