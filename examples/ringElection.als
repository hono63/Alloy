
module examples/ringElection

open util/ordering[Time]
open util/ordering[Process]

sig Time{}
sig Process
{
	succ: Process, // Next process. Not related to Time because the ring topology is static.
	toSend: Process -> Time, // to pool ID
	elected: set Time, // elected as leader during Time
}

// show sample
//run {some toSend and some elected} for 3
run {} for 3 Process, 7 Time

//----------------------------------------------------------------//

fact RingTopology 
{
	all p:Process | Process in p.^succ
}

pred init(t:Time)
{
	// toSend indicates own
	all p:Process | p.toSend.t = p
}

pred step(t,t':Time, p:Process)
{
	let from = p.toSend, to = p.succ.toSend | some id:from.t 
	{
		from.t' = from.t - id
		to.t'   = to.t + (id - p.succ.prevs)
	}
}

pred skip(t,t':Time, p:Process)
{
	p.toSend.t = p.toSend.t'
}

fact Traces
{
	first.init
	all t:Time - last | let t' = t.next | all p:Process |
	  step[t,t',p] or step[t,t',succ.p] or skip[t,t',p]
}

fact DefineElected
{
	no elected.first
	all t:Time - first |
	  elected.t = {p:Process | p in p.toSend.t - p.toSend.(t.prev)}
}

assert AtMostOneElected {lone elected.Time}
check AtMostOneElected for 3 Process, 7 Time

//----------------------------------------------------------------//

pred progress
{
	all t:Time - last | let t' = t.next | 
	  some Process.toSend.t => some p:Process | not skip[t,t',p]
}

assert AtLeastOneElected 
{
	progress and #Time >= #Process.plus[1] => some elected.Time
}
check AtLeastOneElected

//----------------------------------------------------------------//

pred looplessPath
{
	no disj t,t':Time | toSend.t = toSend.t'
}
run looplessPath for 3 Process, 13 Time
