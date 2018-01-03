
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

pred show (b: Book) {
	#Group = 1
	//#Group.(b.addr) = 2
	Group.(b.addr) in Alias
	#Alias = 2
	Alias.(b.addr) in Addr
	#Addr  = 3
	Group in b.names
	Alias in b.names
	//#b.addr >= 1
	}

run show for 6 but 1 Book

