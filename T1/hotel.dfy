class Key { }
class Card {
    var fst: Key;
    var snd: Key;
    
    constructor(fst: Key, snd: Key)
    {
        this.fst := fst;
        this.snd := snd;
    }
 }
class Guest 
{

}
class Payment
{

}
class Desk 
{
    
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
    {
        
    }
}

class RoomService
{
    method Pay(c: Card, g: Guest, p: Payment) 
    {

    }
}