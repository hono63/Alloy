
module 論理系確認/BasicLogic2

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	names: set Name,
	addr: names -> some Target 
	}

pred show1 (b:Book) { // 推移的の例。
	(b.addr).(b.addr) in b.addr
	b.addr & iden = none->none
	//no a:b.addr | a in iden // 何故かこれだとエラー出る。
	//all n:b.names | n != n.(b.addr) // 何故かこれだと上手くいかない。
	}

pred show2 (b:Book) { // 転置。対象閉包の例。
	all n:Name, t:Target | (n->t + ~(n->t)) in b.addr
	}

run show2 for 3 but 1 Book
