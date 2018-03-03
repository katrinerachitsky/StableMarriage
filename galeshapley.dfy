
method Main() 
decreases *{
  print "hello, Dafny\n";
  assert 1 < 2;
  var man0, man1, man2 := new int[3], new int[3], new int[3] ;
  man0[0], man0[1], man0[2] := 0, 1, 2;
  man1[0], man1[1], man1[2] := 1, 0, 2;
  man2[0], man2[1], man2[2] := 0, 1, 2;
  var woman0, woman1, woman2 := new int[3], new int[3], new int[3] ;
  woman0[0], woman0[1], woman0[2] := 1, 0, 2;
  woman1[0], woman1[1], woman1[2] := 0, 1, 2;
  woman2[0], woman2[1], woman2[2] := 0, 1, 2;

  var men: map<int, array<int>> := map[0 := man0, 1 := man1, 2 := man2];
  var women: map<int, array<int>> := map[0 := woman0, 1 := woman1, 2:= woman2];
  var results := matching(men, women);

  var i := 0;
  print "\n final matches are: \n";
  while (i < |results|) && i in results {
    print " man ";
    print i;
    print " woman ";
    print results[i];
    print "\n";
    i := i + 1;
  }
}

method matching(men: map<int, array<int>>, women: map<int, array<int>>) returns (matched_output: map<int, int>)  // matched array is a mapping of women to their respective mate
  // require each person on preference list to be in the women keys mapping, and vice versa for men
  decreases *;
  requires |men| != 0; // requires cardinality of men map to be non-zero
  requires |women| != 0;
  requires |men| == |women| // requires cardinality of men and women maps to be equal
  //requires 0 in men && 0 in women; // both men and women need to start at 0 (man 0 and woman 0)
  requires -1 !in men && -1 !in women;
  requires forall i :: 0 <= i < |men| ==> i in men && men[i] != null && men[i].Length == |men| // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < |women| ==> i in women && women[i] != null && women[i].Length == |women| // checks the same for women's list
  //ensures forall i :: 0 <= i < |women| ==> i in matched_output.Keys;
  //ensures forall i :: 0 <= i < |men| ==> i in matched_output.Values;
  //ensures forall i :: 0 <= i < domain ==> i in matched && exists j :: 0 <= j < domain && matched[i] == j // ensures that the resulting matching includes all original participants (everyone has a match)
  {
    
    //var unmarried_men := men;
    var matched: map<int,int>;
    var currentMan: int := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
    while (|matched| < |men| && currentMan in men.Keys && currentMan !in matched.Values) // while cardinality of matched is less than that of men
      //invariant currentMan in men.Keys && currentMan !in matched.Values;
      //invariant |matched| <= |men|
      //decreases (|women| - |matched|);
      decreases *; 
      //decreases forall i :: 0 <= i < |men| ==> i in men && i !in matched; // amount of free men will decrease
    {
        print "we are now on man ";
        print currentMan;
        print "\n";
        var preferences: array := men[currentMan]; // get preference list for current man
        var currentPrefIndex: int := 0; // set current woman to top of preference list (so that we immediately go for highest ranking woman on currentMan's list)
        while (currentPrefIndex < preferences.Length) // while we have not reached the end of the preferences list
          decreases (preferences.Length - currentPrefIndex)
        {
          print "we are looking at preference array for man: ";
          print currentMan;
          print ", at this index: ";
          print currentPrefIndex;
          print "\n";
          var currentWoman: int := preferences[currentPrefIndex]; // starting at index 0 of preferences list, highestPreferred woman will be named first
          print "woman at that index, on this man's preference list is ";
          print currentWoman;
          print "\n";
          if (currentWoman !in matched.Keys && currentWoman in women) { // if the highestPreferred woman is not found in the matched mapping == if highest preferred woman free
            print "woman is not currently engaged\n";
            matched := matched[currentWoman := currentMan]; // add current highestpreferred woman and current man to mapping
            print "woman: ";
            print currentWoman;
            print" man: ";
            print currentMan;
            print "\n";
            break;
          } else if (currentWoman in matched.Keys && currentWoman in women) { // if current woman is matched
            var preferences: array := women[currentWoman]; // get woman's preference list
            var man_matched: int := matched[currentWoman]; // find woman's current mate
            var currentMan_index: int:= Find(preferences, currentMan); // get index on preference list of woman for current man
            var man_matched_index: int := Find(preferences, man_matched); // get index on preference list of woman for current mate
            if (currentMan_index < man_matched_index) { // if index of current man is higher on preference list than the matched mate
              matched := map i | i in matched && i != currentWoman :: matched[i]; // remove original woman-man pair from matched
              matched := matched[currentWoman := currentMan]; // add current Man with his highestpreferred woman to mapping
              print "woman: ";
              print currentWoman;
              print" man: ";
              print currentMan;
              print "\n";
              break;
            }
        }
        currentPrefIndex := currentPrefIndex + 1; // move on to the next woman for next iter of while loop
      }
      // man should be matched by this point
      currentMan := getFreeMan(men.Keys, matched.Values); // calls getFreeMan to find first man from set of men and finds a man not in the matched values yet
      print "new man is ";
      print currentMan;
      print "\n";
    } // end of men needing a match
    matched_output := matched;
    return matched_output;
}

method getFreeMan(men: set<int>, engagedMen: set <int>) returns (index: int) 
  // requires exists some index between 0 and men cardinality such that index in men
  requires |men| > 0;
  ensures index < |men| ==> index in men && index !in engagedMen;
  //requires exists i :: 0 <= i < |men| && i in men && i !in engagedMen;
  //ensures index < |men| ==> forall i :: 0 <= i < index && !(i in men && i !in engagedMen);
  //ensures index >= |men| ==> !(exists i :: 0 <= i < |men| && i in men && i !in engagedMen); //forall i :: 0 <= i < |men| && !(i in men && i !in engagedMen);;
  {
  index := 0;
  while (index < |men|)
  invariant 0 <= index <= |men|;
 // invariant forall i :: 0 <= i < index ==> ()
  {
    if (index in men && index !in engagedMen)
    {
      return index;
    } else {
      index := index + 1;
    }
  }
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
