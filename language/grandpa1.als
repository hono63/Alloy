
module language/grandpa1

abstract sig Person 
{
	father: lone Man,
	mother: lone Woman,
	//Lfather: mother.husband - father, //上手くいかない…
	//Lmother: father.wife    - mother,
}
sig Man extends Person
{
	wife: lone Woman
}
sig Woman extends Person
{
	husband: lone Man
}

fact Biology
{// 自分の祖先にはなれない
	no p:Person | p in p.^(mother + father)
}
fact Terminology
{// wifeはhusbandの転置である。
	wife = ~husband 
}
fact SocialConvention
{// 近親相姦を避ける
	no (wife + husband) & ^(mother + father) 
}

assert NoSelfFather
{
	no m: Man | m = m.father
}
check NoSelfFather

fun grandpas (p:Person): set Person
{
	//p.(mother + father).father
	// 継母、継父を含めるようにする。
	let parent = mother + father + father.wife + mother.husband |
	  p.parent.parent & Man
}
pred ownGrandpa (p:Person)
{
	p in grandpas[p]
}
run ownGrandpa for 4
