
module 論理系確認/BasicLogic

//open tour/addressBook3

abstract sig Target {}
sig Addr extends Target {}

abstract sig Name extends Target {}
sig Alias, Group extends Name {}

sig Book { 
	names: set Name,
	addr: names -> some Target 
	}

pred show0 (b:Book, n1,n2:b.names, g:Group, al:Alias, a:Addr) {
	g in n1 and al in n2 and a in b.addr[n2]
	//#g = 1
	//g.(b.addr) in al
	//#al = 2
	//al.(b.addr) in a
	//#a  = 3
	}

pred show1 {
	#Book = 1 
	#Group = 1 
	#Alias = 2 
	#Addr > 0
	all b:Book | #b.names = 3 and #b.addr = 4
	}

pred show2 {
	#Book = 1 
	#Group = 1 
	#Alias = 1 
	#Addr > 0
	}

pred show3 (b:Book) { // 成功
	#Group = 1 
	all g:Group | g in b.names and g.(b.addr) in Alias
	#Alias = 2 
	all a:Alias | a in b.names and a.(b.addr) in Addr
	all a:Alias | a in (b.names).(b.addr)
	#Addr = 3
	all ad:Addr | ad in (b.names).(b.addr)
	}

run show3 for 6 but 1 Book

