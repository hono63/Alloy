
module language/grandpa1

abstract sig Person 
{
	father: lone Man,
	mother: lone Woman
}
sig Man extends Person
{
	wife: lone Woman
}
sig Woman extends Person
{
	husband: lone Man
}

fact 
{
	no p:Person | p in p.^(mother + father)
	wife = ~husband // wifeはhusbandの転置である。
}

assert NoSelfFather
{
	no m: Man | m = m.father
}
check NoSelfFather

fun grandpas (p:Person): set Person
{
	p.(mother + father).father
}
pred ownGrandpa (p:Person)
{
	p in grandpas[p]
}
run ownGrandpa for 4
