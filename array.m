load "setupM.m";

procedure next(~indices, n)
/*
This takes a list of numbers indices = [k_1, k_2, ... k_l] such that 1 le k_i le n.
It modifies the list by incrementing k_l by 1, if after this k_l = n+1 it sets k_l = 1 and k_{l-1} is then incremented, and so on
If k_1 reaches n+1 all entries will have been set to 1. 
EXAMPLE:
 if list = [1,1] and n = 2 then
 after next(~list,2), list =  [1,2],
 after next(~list,2), list =  [2,1],
 after next(~list,2), list =  [2,2],
 after next(~list,2), list =  [1,1].

The idea here is that if we have a big list xs and want to find all sublists of length 3, then set index = [1,1,1]
and find all sublists calling next(index, #xs) until it loops back down to [1,1,1].
*/
    for i in [#indices .. 1 by -1] do 
        indices[i] := indices[i] + 1;
        if indices[i] eq n+1 then 
            indices[i] := 1;
        else 
            break;
        end if;    
    end for;     
end procedure;

function BuildPIArray(numSums, prods : filename := "") 
/****
This function takes a list of elements prods from M.
Computes all sums x of multisets of numSums elements from prods.
Then test if these x's are PIs whose final projection (p = x*x) sits below its initial projection q = xx*)
Returns a tuple PIarray, keySet, 
where PIarray is an associative array of pairs <x,q> index by their initial projections. 
setKeys is the set of initian projections used.  
If a filename is given, write the AssociativeArray to filename.m
****/
	//printf "Building AssociativeArray directly from allSums.\n\n";
	PIarray := AssociativeArray(M); //Make a hashtable/dictionary/AssociativeArray with index set M.
	keys := []; // List of elements of M we actually use as keys (in particular these will be projections) 

	//for status printing
	tenpc := (#prods)^numSums div 10;  
	count := 1;

	//loop over all multisets of prods with numSum elements
	//form their sum and check if it is a PI whose final projection sits below their initial projection.  
	index := [1 : i in [1..numSums]]; //list of 1's of length numSums ([1,1,...,1])
	endIndex := index;
	repeat
		x := &+(prods[index]); // set x to be the sum of the elements of prod indexed by index. 
		next(~index, #prods); // increment our index

		p := Adjoint(x)*x; // potential initial projection
		if x*p eq x then // first test if x x* x = x, that is, if x is a PI. 
			q := x*Adjoint(x); // final projection of x. 
			if p*q eq q then // then test if the final projection sits below the initial projection. 
				if IsDefined(PIarray, p) then
					// true if we have already added a PI with initial projection p
					Append(~PIarray[p],<x,q>); //Add <x,q> to the list of PIs with intial projection p
				else 
					//false if we have not yet added a PI with initial projection p yet
					Append(~keys, p); //add p to the set of keys
					PIarray[p] := [<x,q>]; //make the singleton list <x,q> the list of PIs with initial projection p
				end if;	
			end if;
		end if;

		// status printing start
		if count mod tenpc eq 0 then
			printf "%o%% ... ", 10 * count div tenpc;
			if 10 * count div tenpc eq 100 then 
				printf "\n";
			end if;
		end if;
		count := count + 1;
		// end status printing

	until index eq endIndex;

	print "Removing duplicates";
	keySet := Seqset(keys);
	for p in keySet do
		PIarray[p] := Seqset(PIarray[p]);
	end for;
 	
	// if a filename is given, store the AssociativeArray
	if #filename gt 0 then 
		filename := filename cat ".m";
		printf "Saving AssociativeArray to %o.\n", filename;
		file := Open(filename, "a");
		// store the keys first
		line := "keys := " cat Sprint(keySet) cat ";";
		Puts(file, line);		
		// setup the AssociativeArray
		line := "allPIs := AssociativeArray(M);";
		Puts(file, line);
		for p in keySet do
			line := "allPIs[" cat Sprint(p) cat "] := " cat Sprint(PIarray[p]) cat ";";
			Puts(file, line);
		end for;
		delete file; //unassing and close file.
	end if;			
	printf "Done!\n\n";
	return PIarray, keys;
end function;

function BuildMaps(PIProjectionPairs, p)
/*
Given a list PIProjectionPairs of pairs <x,q> of PIs x with final projection q and all with initial projections p,
finds all those pairs <x,y> that satisfy the L_2 relations 
with <x,q1>,<y,q2> in PIProjectionPairs. 
Returns a list contianing tuples of the form <{x,y},p>.
*/
	returnList := [];
	for i in [1 .. #PIProjectionPairs] do
		x := PIProjectionPairs[i];
		for j in [i .. #PIProjectionPairs] do
			y := PIProjectionPairs[j];
			if x[2] + y[2] eq p then 
				Append(~returnList,<{x[1],y[1]},p>);
			end if;
		end for;
	end for;
	return returnList;
end function;

procedure MapsToCSVFile(maps, filename)
	file := Open(filename, "a");
	for map in maps do
		PIs := Setseq(map[1]);
		line := "";
		if #PIs eq 2 then
			line := Sprint(PIs[1]) cat "," cat Sprint(PIs[2]) cat "," cat Sprint(map[2]); 
		else
			line := Sprint(PIs[1]) cat "," cat Sprint(PIs[1]) cat "," cat Sprint(map[2]); 
		end if;
	Puts(file, line);
	end for;
	delete file; //unassing and close file I hope. 
end procedure;

procedure MapsToFile(xss, keys, filenamebasis)
/*
Given an AssociativeArray of PIs xss index by initial projections in keys
find all maps using those PIs.
Write the maps to a csv files, one per "block".
The file for the p'th block is named filnamebasis-p.csv
*/
	maps := [];	
	count := 1;
	filename := "";
	printf "Building maps...\n";
	printf "Have to loop over %o blocks. \n", #keys;
	for p in keys do
		printf "Working on block with initial projection %o\n", p;
		maps := BuildMaps(Setseq(xss[p]), p);
		filename := filenamebasis cat "-" cat Sprint(p) cat ".csv";
		MapsToCSVFile(maps, filename);
		printf "Completed, %o blocks remaining. \n", #keys-count;
		count := count+1;
	end for;
end procedure;

procedure StorePIs(numSums, numProds, pisFilename)
	printf "\nBuilding set of all products of length up to %o.\n\n", numProds;
	allPaths := {&*letters : letters in CartesianPower(setM,numProds)};
	printf "There are %o products of length %o.\n\n", #allPaths, numProds;
//	printf "Building set of all sums at most %o terms of products.\n", numSums;
//	allSums := {&+words : words in Multisets(allPaths, numSums)};
	printf "Building partial isometries that are a sum of at most %o terms of profucts.\n", numSums;	
	xss, keys := BuildPIArray(numSums, Setseq(allPaths) : filename := pisFilename);
//	delete allSums;
	sum := 0;
	for p in keys do
		sum := sum + #(xss[p]);
	end for;
	printf "There are %o partial isometries.\n\n", sum;
end procedure;

procedure RunFromNothing(numProds, numSums, mapsFilenameBasis : pisFilename := "")
	printf "\nBuilding set of all products of length up to %o.\n\n", numProds;
	//allPaths := BuildProducts(numProds-1);
	allPaths := {&*letters : letters in CartesianPower(setM,numProds)};
	printf "There are %o products of length %o.\n\n", #allPaths, numProds;
//	printf "Building set of all sums at most %o terms of products.\n", numSums;
//	allSums := {&+words : words in Multisets(allPaths, numSums)};
	printf "Building partial isometries that are a sum of at most %o terms of profucts.\n", numSums;	
	xss, keys := BuildPIArray(numSums, Setseq(allPaths) : filename := pisFilename);
	MapsToFile(xss, keys, mapsFilenameBasis);
end procedure;

