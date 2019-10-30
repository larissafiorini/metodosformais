method Main(){
    var c := {1,2,3,4};
    assert (set x | x in c && x < 2 ) == {1};

    var c2 := set x: nat, y: nat | x < 2 && y < 2 :: (x, y);
}