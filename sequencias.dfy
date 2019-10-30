method Main() {
    var s := [1, 2, 3, 4, 5];
    assert s[|s| -1] == 5;
    assert s[|s|-1..|s|] == [5];
    assert s[1..] == [2, 3, 4, 5];
    assert s[..|s|-1] == [1, 2, 3, 4];
    assert s == s[0..] == s[..|s|] == s[0..|s|] == s[..];
}

predicate sorted(a: seq<int>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

// method busca(a: array<nat>, e: nat) returns (r: bool)
// ensures r <==> e in a[..]