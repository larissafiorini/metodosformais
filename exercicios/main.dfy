//function: especifica. Fatorial: N->N

function Fat(n:nat):nat{
    if (n==0)
    then 1
    else n*Fat(n-1)
}

//method: implementa
method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n) 
{
    f :=1;
    var i:= n;
    while(i>0)
    invariant 0 <= i <= n
    {
        f := f*1;
        i := i-1;
    }
}


// predicate: especifica
predicate Par(n:nat){
    n%2==0
}

method Dobro(x:int) returns (r:int)
ensures r==2*x

method Triplo(x:int) returns (r:int)
ensures r==3*x
{
    var y := Dobro(x);
    r:= x+y;
}
