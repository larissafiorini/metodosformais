module hotel
open util/ordering [Time]

sig Key, Time {}
sig Card {
	fst, snd: Key
}
sig Room {
	key: Key one-> Time
}
one sig Desk {
	issued: Key-> Time,
	prev: (Room-> lone Key)-> Time
}
sig Guest {
	cards: Card-> Time
}

pred init (t: Time) {
	Desk.prev.t = key.t
	Desk.issued.t = Room.key.t and no cards.t
}


sig RoomService {
	service_payment: Payment lone -> Time  
}

sig Payment{}

pred pay (t, t':Time, c: Card, g: Guest, p: Payment) {
	// Pre-condicao: card fornecido no pagamento corresponde ao card do guest
	some cardguest: g.cards.t {
		c in cardguest
	}

	// Pre-condicao: service_payment nao recebeu pagamento
	no service_payment.t

	// Pos-condicao: pagamento foi atribuido a service_payment
	RoomService.service_payment.t' = p
}

pred checkin (t, t': Time, r: Room, g: Guest) {
	some c: Card {
		c.fst = r.(Desk.prev.t)
		c.snd not in Desk.issued.t
		cards.t' = cards.t ++ g-> c
		Desk.issued.t' = Desk.issued.t + c.snd
		Desk.prev.t' = Desk.prev.t ++ r-> c.snd
	}
	key.t = key.t'
}

pred enter (t, t': Time, r: Room, g: Guest) {
	some c: g.cards.t |
	let k = r.key.t {
		c.snd = k and key.t' = key.t
			or c.fst = k and key.t' = key.t ++ r-> c.snd
	}
	issued.t = issued.t' and (Desk<:prev).t = prev.t'
	cards.t = cards.t'
}

fact Traces {
	init [first]
	all t: Time - last |
	some g: Guest, r: Room |
	checkin [t, next [t], r, g] or enter [t, next [t], r, g]
}

assert NoIntruder {
	no t1: Time, disj g, g': Guest, r: Room |
	let t2 = next [t1], t3 = next [t2], t4 = next [t3] {
		enter [t1, t2, r, g]
		enter [t2, t3, r, g']
		enter [t3, t4, r, g]
	}
}

// check NoIntruder for 6 but 12 Time, 3 Guest, 3 Room

run pay for 6 but 12 Time, 1 Guest, 1 Room, 1 Payment, 1 RoomService

// Fonte: https://www.doc.ic.ac.uk/project/examples/2007/271j/suprema_on_alloy/Web/tutorial1_1.php
