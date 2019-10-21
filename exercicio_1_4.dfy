/*
sum(n)=0, se n=0
sum(n)=n+sum(n-1), se n>0
*/

function Sum(n:nat):nat{
    if(n==0)
    then 0
    else n+ Sum(n-1)
}

method computesum(n:nat) returns (s:nat)
ensures s==Sum(n){
   // s := n* (n+1) /2;
   s:=0;
   var i:=0;
   while(i<n)
   invariant 0<=i<=n
   invariant s ==Sum(i)
{
    i:=i+1;
    s:=s+i;
}
}

/* exercicio_1_3*/
function Fib(n:nat):nat{
    if(n<2)
    then n
    else Fib(n-2) + Fib(n-1)
}

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    x:=0;
    var y:=1;
    var i:= 0;
    while(i<n)
    invariant 0 <=i<=n
    invariant x==Fib(i) && y==Fib(i+1)
    {
        x,y:=y,x+y; 
        i:=i+1;
    }
}
// aula 21.10.19
method Busca(a:array<nat>, e:nat) returns (r:bool)
ensures r <==> exists i :: 0 <= i < a.Length && a[i]==e
{
    var pos := 0;
    while pos < a.Length
    invariant 0 <= pos <= a.Length
    invariant forall i :: 0 <= i < pos ==> a[i] != e
    {
        if a[pos] == e
        {
            return true;
        }
        pos := pos+1;
    }
    return false;
}


method FindMax(a:array<int>) returns (i:int)
requires a.Length > 0
ensures 0 <= i < a.Length
ensures forall j :: 0 <= j < a.Length ==> a[i] >= a[j] 
{
    
}
