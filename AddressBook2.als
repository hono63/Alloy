
module tour/addressBook2

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	addr: Name -> Target
	}
	{ // factでなくてこちらに書くことも可能。
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr   // Aliasから写像(addr)される対象はひとつだけ(lone)
	}	

//-----------------------------------------------------------------//

fact {
	all b: Book | no n: Name | n in n.^(b.addr)	// ^は1回以上適用という意味。nから辿っていってもn自身にはたどり着かない、というfact(常に成り立つ制約)
	}

pred show1 (b: Book) {some b.addr}
pred show2 (b: Book) {some Alias.(b.addr) } // Aliasの例を見たい
run show2 for 3 but 1 Book

