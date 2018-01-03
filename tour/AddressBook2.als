
module tour/addressBook2

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	names: set Name,
	addr: names -> some Target // Bookに含まれるnames集合からのaddr写像には必ず1つ以上のTargetが存在する。
	//addr: Name -> Target	// こちらはName空間からTarget空間への写像？
	}
	{ // factでなくてこちらに書くことも可能。
	no n: Name | n in n.^(addr)
	all a: Alias | lone a.addr   // Aliasから写像(addr)される対象はひとつだけ(lone)
	}	

//-----------------------------------------------------------------//

fact {
	all b: Book | no n: Name | n in n.^(b.addr)	// ^は1回以上適用という意味。nから辿っていってもn自身にはたどり着かない、というfact(常に成り立つ制約)
	}

pred add (b, b': Book, n: Name, t: Target) {
	b'.addr = b.addr + n -> t
	}
pred del (b, b': Book, n: Name, t: Target) { // tの引数がないと、グループの中からひとつだけ削除、ができない。
	b'.addr = b.addr - n -> t
	}
fun lookup (b: Book, n: Name) : set Addr { 
	n.^(b.addr) & Addr // Addr全体の空間との共通部分をとる
	}
pred show1 (b: Book) {some b.addr}
pred show2 (b: Book) {some Alias.(b.addr) } // Aliasの例を見たい
run show2 for 3 but 1 Book

//-----------------------------------------------------------------//

assert lookupYields { // lookupしたらアドレスは何かしら存在するよね。
	all b:Book, n:b.names | some lookup[b,n]
	}
check lookupYields for 4 but 1 Book

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


