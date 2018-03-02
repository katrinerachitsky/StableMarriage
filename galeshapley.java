
method Main() 
decreases *{
  print "hello, Dafny\n";
  assert 1 < 2;
  var a := new int[2] ;
  a[0], a[1] := 0, 1;
  var b := new int[2] ;
  a[0], a[1] := 1, 0;
  var men: map<int, array<int>> := map[0 := a, 1 := b];
  var women: map<int, array<int>> := map[0 := a, 1 := b];
  var results := matching(men, women);
  
  
  /*var i := 0;
  while i < |results| {
    print results[i];
    i := i + 1;
  }*/
  //var preflist2: array<int> := [1,0];
   //var men: map<int, array<int>> := map[0 := preflist, 1 := preflist2];
   //var women := map[0 := preflist, 1 := preflist2];
   //var results := matching(men, women);
  //var men: map<int, array<int>> := {0 := preflist};
}

method matching(men: map<int, array<int>>, women: map<int, array<int>>) returns (matched_output: map<int, int>)  // matched array is a mapping of women to their respective mate
  // require each person on preference list to be in the women keys mapping, and vice versa for men
  decreases *;
  requires |men| != 0; // requires cardinality of men map to be non-zero
  requires |women| != 0;
  requires |men| == |women| // requires cardinality of men and women maps to be equal
  //requires 0 in men && 0 in women; // both men and women need to start at 0 (man 0 and woman 0)
  requires forall i :: 0 <= i < |men| ==> i in men && men[i] != null && men[i].Length == |men| // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < |women| ==> i in women && women[i] != null && women[i].Length == |women| // checks the same for women's list
  //ensures forall i :: 0 <= i < |women| ==> i in matched_output.Keys;
  //ensures forall i :: 0 <= i < |men| ==> i in matched_output.Values;
  //ensures forall i :: 0 <= i < domain ==> i in matched && exists j :: 0 <= j < domain && matched[i] == j // ensures that the resulting matching includes all original participants (everyone has a match)
  {
    var currentMan: int := 0;
    var matched: map<int,int>;
    while (currentMan !in matched.Values && currentMan in men)
      //decreases *;
      //decreases forall i :: 0 <= i < |men| ==> i in men && i !in matched; // amount of free men will decrease
    {
      var preferences: array := men[currentMan]; // get preference list for current man
      var currentPrefIndex: int := 0; // set current woman to top of preference list (so that we immediately go for highest ranking woman on currentMan's list)
      while (currentPrefIndex < preferences.Length) // while we have not reached the end of the preferences list
        decreases (preferences.Length - currentPrefIndex)
        //decreases *;
        //decreases (preferences.Length - currentPrefIndex); // loop termination will occur, because preference list will be iterated through and amount of women to choose from gets smaller
     {
        var currentWoman: int := preferences[currentPrefIndex]; // starting at index 0 of preferences list, highestPreferred woman will be named first
        if (currentWoman !in matched.Keys && currentWoman in women) { // if the highestPreferred woman is not found in the matched mapping == if highest preferred woman free
          matched := matched[currentWoman := currentMan]; // add current highestpreferred woman and current man to mapping
          break;
        } else if (currentWoman in matched.Keys && currentWoman in women) { // if current woman is matched
            var preferences: array := women[currentWoman]; // get woman's preference list
            var man_matched: int := matched[currentWoman]; // find woman's current mate
            var currentMan_index: int:= Find(preferences, currentMan); // get index on preference list of woman for current man
            var man_matched_index: int := Find(preferences, man_matched); // get index on preference list of woman for current mate
            if (currentMan_index < man_matched_index) { // if index of current man is higher on preference list than the matched mate
              matched := map i | i in matched && i != currentWoman :: matched[i]; // remove original woman-man pair from matched
              matched := matched[currentWoman := currentMan]; // add current Man with his highestpreferred woman to mapping
              break;
            }
        }
        currentPrefIndex := currentPrefIndex + 1; // move on to the next woman for next iter of while loop
      } // end of preferences list
      // man should be matched by this point
      currentMan := currentMan + 1;
    } // end of men needing a match
    matched_output := matched;
    return matched_output;
}

method Find(a: array<int>, key: int) returns (index: int)
   requires a != null
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
   {
      if a[index] == key { return; }
      index := index + 1;
   }
   index := -1;
}
