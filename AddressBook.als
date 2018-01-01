
module tour/addressBook1

sig Name, Addr {} // シグネイチャはオブジェクトの集合を表す。
sig Book{
	addr: Name -> lone Addr // loneは多重度を表す。ここでは名前が高々１つのアドレスに紐付けられている。
}

//-----------------------------------------------------------------//

pred show0 {}
pred show1 (b:Book) {
	#b.addr > 1 // #は含まれる対応の数を表す。
}
pred show2 (b: Book) { // １つの名前が複数アドレスに対応。この制約を満たすインスタンスは存在しない。
	#b.addr > 1
	some n: Name | #n.(b.addr) > 1
}
pred show3 (b: Book) { // 複数のアドレスは存在することを確認したい。
	#b.addr > 1
	#Name.(b.addr) > 1
}

// インスタンスを探索する範囲のスコープを制限している。ここでは各オブジェクトが高々３つ。ただしBookは１つ。
//run show3 for 3 but 1 Book

//-----------------------------------------------------------------//

pred add (b, b': Book, n: Name, a: Addr) {
	b'.addr = b.addr + n -> a
}
pred del (b, b': Book, n: Name) { // nに紐づく全てのアドレスをbから削除する。
	b'.addr = b.addr - n -> Addr
}
fun lookup (b: Book, n: Name) : set Addr { // funはfunctionのこと。この中では制約ではなく式を書く。名前nが指し示すaddr全ての集合。
	n.(b.addr)
}
pred showAdd (b, b': Book, n: Name, a: Addr) {
	add [b, b', n, a]
	#Name.(b'.addr) > 1 // これは調べるための制約。Name集合内の事後b'のaddr紐の数が2以上。
}
// 2 Bookでaddの事前状態と事後状態を示したい。
run showAdd for 3 but 2 Book

//-----------------------------------------------------------------//

assert delUndoesAdd1 { // 追加したnを消したら同じ状態になるよね？(=undo)
	all b,b',b'': Book, n: Name, a:Addr |
		add [b, b', n, a] and del [b', b'', n] implies b.addr = b''.addr
}
assert delUndoesAdd2 { // nが事前のアドレス帳bに存在しない、という条件を追加。
	all b,b',b'': Book, n: Name, a:Addr |
		no n.(b.addr) and add [b, b', n, a] and del [b', b'', n] implies b.addr = b''.addr
}
assert addIdempotent { // 同じ名前を追加しても帳bは変化しないよね。
	all b,b',b'': Book, n: Name, a:Addr |
		add[b, b', n, a] and add[b', b'', n, a] implies b'.addr = b''.addr
}
assert addLocal { // 違う名前の登録は影響ないよね。
	all b,b': Book, n,n': Name, a: Addr |
		add[b,b',n,a] and n != n' implies lookup[b,n'] = lookup[b',n']
}

check delUndoesAdd1 for 3
check delUndoesAdd2 for 10 but 3 Book // 妥当だと数学的に証明されたわけではないが、膨大なテストケースを網羅できている。
