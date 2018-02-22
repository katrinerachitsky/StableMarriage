method matching(men: map<int, array<int>>, women: map<int, array<int>>, domain: int) returns (matched: map<int, int>) 
  requires !(men.Items == {}) && 0 in men; // requires that the set of items in the map is non-empty
  requires !(women.Items == {}) && 0 in women; 
  requires |men| != 0;
  requires forall i :: 0 <= i < domain ==> i in men && men[i] != null && men[i].Length == domain // checks that for each possible key in domain, this key exists in the mapping, that the array (value) associated with this key is non-empty and that it contains exactly the amount of entries as each map (the domain)
  requires forall i :: 0 <= i < domain ==> i in women && women[i] != null && women[i].Length == domain // checks the same for women's list
  //ensures forall i :: 0 <= i < domain ==> i in matched && exists j :: 0 <= j < domain && matched[i] == j // ensures that the resulting matching includes all original participants (everyone has a match)
  {
    var currentMan: int := 0;
    var freeMen: map := men;
    while (!(freeMen.Items == {}) && currentMan in freeMen)
      decreases freeMen.Items; // amount of free men will decrease
    {
      var preferences: array := freeMen[currentMan]; // get preference list for current man
      var currentWoman: int := 0; // set current woman to top of preference list (so that we immediately go for highest ranking woman on currentMan's list)
      while currentWoman < preferences.Length // while we have not reached the end of the preferences list
      	decreases (preferences.Length - currentWoman); // loop termination will occur, because preference list will be iterated through and amount of women to choose from gets smaller
     {
        var highestPrefWoman: int := preferences[currentWoman]; // starting at index 0 of preferences list, highestPreferred woman will be named first
        if (highestPrefWoman !in matched.Values){ // if the highestPreferred woman is not found in the matched mapping
          matched[currentMan := highestPrefWoman]; // add current Man with his highestpreferred woman to mapping
        }
      }
    }
}