class Key 
{
    var value: nat;

    constructor(v:nat)
    ensures value == v
    {
        value := v;
    }
}
class Card {
    var guests: seq<Guest>;
    var fst: Key;
    var snd: Key;
    
    constructor(key1: nat, key2: nat)
    ensures fst.value == key1 && snd.value == key2
    ensures fresh(fst) && fresh(snd)
    {
        fst := new Key(key1);
        snd := new Key(key2);
        guests := [];
    }
 }
class Guest 
{
    var cards: seq<Card>;

    constructor(c: seq<Card>)
    requires |c| > 0
    {
        cards := c;
    }
}

class Desk 
{
    var issued: seq<Key>;
    var prv: Room?;

    constructor(p: Room)
    {
        issued := [];
        prv := p;
    }
}

class Room
{
    var key: Key
    constructor(key: Key)
    {
        this.key := key;
    }
    method Checkin(g: Guest)
    {

    }

    method Enter(g: Guest, d: Desk) 
    requires |g.cards| > 0
    requires exists i :: 0 <= i < |g.cards| && (g.cards[i].fst == key || g.cards[i].snd == key)
    ensures exists i :: 0 <= i < |g.cards| && g.cards[i].snd == key
    modifies this
    {
        var i := 0;
        var count := |g.cards|;

        while(i < count)
        {
            if (g.cards[i].fst == key)             
            {
                key := g.cards[i].snd;
                break;
            }
            i := i + 1;
        }
        
        assume exists i :: 0 <= i < |g.cards| && g.cards[i].snd == key;
    }
}

class Payment
{
    var value: nat
}

class RoomService
{
    var servicePayment: Payment?
    method Pay(c: Card, g: Guest, p: Payment) 
    requires servicePayment == null
    requires exists i :: 0 <= i < |g.cards| && (g.cards[i] == c)
    ensures servicePayment != null
    modifies this
    {
        servicePayment := p;
    }
}