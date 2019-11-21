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
    var prv: Room;

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

    method Enter(g: Guest) 
    requires exists i :: 0 <= i < |g.cards| && (g.cards[i].fst == key || g.cards[i].snd == key);
    requires |g.cards| > 0
    {
        var i := 0;
        var count := |g.cards|;

        while(i < count)
        {
            if (g.cards[i].fst == key) 
            {

            }
            else if (g.cards[i].snd == key) 
            {
                
            }
            i := i + 1;
        }
    }
}

class Payment
{

}

class RoomService
{
    method Pay(c: Card, g: Guest, p: Payment) 
    {

    }
}