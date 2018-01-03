
module 論理系確認/BasicLogic2

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	names: set Name,
	addr: names -> some Target, 
	//relation: Target -> Target
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

pred show3 (b:Book) { // 推移閉包の例。失敗
	/*some n:Name, t1,t2:Target | 
	  n->t1 in b.addr and n->t2 in b.addr 
	  and ^(Name->Target) - n->t != none->none*/
	}

pred show4 (b:Book) { // 反射的。
	iden & Target->Target in b.addr
	#b.addr = 4
	}

pred show5 (b:Book) { // 推移的
	b.addr = ^(Target->Target) - iden
	}

pred show6 (b:Book) { // 反射推移閉包。失敗。
	b.relation = *(Target->Target)
	//*r = ^r + iden
	}

run show6 for 4 but 1 Book
