%%% -*- Mode: Prolog; Module: einstein; -A*-


:- module(einstein, [
              doit/1,
              doit_enums/1,
              declare_enums/0
              ]).
              

%% The so-called "Einstein puzzle":
%% From, e.g., https://www.freecodecamp.org/news/einsteins-riddle/
/****
There are 5 houses painted five different colors.
In each house lives a person with a different nationality.
These five owners drink a certain type of beverage, smoke a certain brand of cigar, and keep a certain pet.
No owners have the same pet, smoke the same brand of cigar, or drink the same beverage.

The Brit lives in the red house
The Swede keeps dogs as pets
The Dane drinks tea
The green house is on the left of the white house
The person who smokes Pall Malls rears birds
The owner of the yellow house smokes Dunhill
The green house’s owner drinks coffee
The man living in the center house drinks milk
The Norwegian lives in the first (leftmost) house
The man who smokes Blends lives next to the one who keeps cats
The man who keeps horses lives next to the man who smokes Dunhill
The owner who smokes BlueMaster drinks beer
The German smokes Princes
The Norwegian lives next to the blue house
The man who smokes Blends has a neighbor who drinks water
Now to solve, tell me who owns the fish?
****/

%% load from parent directoryy, with consult(examples/einstein).

:- use_module(z3).

%% functions people->X : pet, owns, drinks, smokes

assertions(L) :-
    L = [
        distinct(yellowhouse:int, greenhouse, redhouse, bluehouse, whitehouse),
        distinct(norwegian:int, brit, swede, dane, german),
        distinct(cats:pet_enum, birds, horses, dogs, fish),
        distinct(beer:beverage_enum, water, milk, coffee, tea),
        distinct(dunhill:smoke_enum, blends, prince, pallmall, bluemaster),

        distinct(owner(yellowhouse):int, owner(greenhouse), owner(redhouse), owner(bluehouse), owner(whitehouse)),
        distinct(smokes(norwegian):smoke_enum, smokes(brit), smokes(swede), smokes(dane), smokes(german)),
        distinct(pet(norwegian):pet_enum, pet(brit), pet(swede), pet(dane), pet(german)),
        distinct(drinks(norwegian):beverage_enum, drinks(brit), drinks(swede), drinks(dane), drinks(german)),

        %% The Brit lives in the red house
        owner(redhouse) = brit,
        %% The Swede keeps dogs as pets
        pet(swede) = dogs,
        %% The Dane drinks tea
        drinks(dane) = tea,
        
        %% The green house is on the left of the white house
        greenhouse:int = whitehouse - 1,
        
        %% The person who smokes Pall Malls rears birds
        smokes(pallmallbirdperson) = pallmall and pet(pallmallbirdperson) = birds and between(pallmallbirdperson, 1, 5),

        %% The owner of the yellow house smokes Dunhill
        owner(yellowhouse) = dunhillsmoker:int and smokes(dunhillsmoker) = dunhill and between(dunhillsmoker, 1, 5),
        
        %% The green house’s owner drinks coffee
        drinks(owner(greenhouse)) = coffee,

        %% The man living in the center house drinks milk
        drinks(owner(3)) = milk,

        %% The Norwegian lives in the first (leftmost) house
        owner(1) = norwegian,

        %% The man who smokes Blends lives next to the one who keeps cats:
        smokes(blendssmoker) = blends and pet(catkeeper) = cats and ((blendssmoker = catkeeper - 1) or (blendssmoker = catkeeper + 1))
                                                           and between(blendssmoker, 1, 5) and between(catkeeper, 1, 5),

        %% The man who keeps horses lives next to the man who smokes Dunhill
        pet(horsekeeper) = horses and smokes(dunhillsmoker) = dunhill and ((horsekeeper = dunhillsmoker+1) or (horsekeeper = dunhillsmoker - 1 ))
                                                              and between(horsekeeper, 1, 5) and between(dunhillsmoker, 1, 5),

        %% The owner who smokes BlueMaster drinks beer
        %% drinks(smoker(bluemaster)) = beer,
        smokes(bluemasterbeerperson) = bluemaster and drinks(bluemasterbeerperson) = beer
               and between(bluemasterbeerperson, 1, 5),

        %% The German smokes Princes
        smokes(german) = prince,

        %% The Norwegian lives next to the blue house
        %% (owner(y)=norwegian and (y = bluehouse-1 or y = bluehouse + 1)) and y>=1 and y=<5,
        %% since we identify people and houses we can write it like this:
        (norwegian = bluehouse-1 or norwegian = bluehouse + 1),

        
        %% The man who smokes Blends has a neighbor who drinks water
        smokes(blendssmoker) = blends and drinks(waterdrinker) = water and ((blendssmoker = waterdrinker - 1) or (blendssmoker = waterdrinker + 1))
             and between(blendssmoker, 1, 5) and between(waterdrinker, 1, 5),
                
        true
    ].


basic_assertions(L) :- L = [
                               between(greenhouse, 1, 5),
                               between(bluehouse, 1, 5),
                               between(redhouse, 1, 5),
                               between(whitehouse, 1, 5),
                               between(yellowhouse, 1, 5),

                               dane >=1, dane =<5,
                               swede >=1, swede =<5,
                               german >=1, german =<5,
                               brit >=1, brit =<5,
                               norwegian >=1, norwegian =<5,

                               owner(greenhouse) = greenhouse,
                               owner(bluehouse) = bluehouse,
                               owner(redhouse) = redhouse,
                               owner(whitehouse) = whitehouse,
                               owner(yellowhouse) = yellowhouse,

                               %% not needed if enums are used:
                               isoneof(pet(1), dogs, fish, horses, cats, birds),
                               isoneof(pet(2), dogs, fish, horses, cats, birds),
                               isoneof(pet(3), dogs, fish, horses, cats, birds),
                               isoneof(pet(4), dogs, fish, horses, cats, birds),
                               isoneof(pet(5), dogs, fish, horses, cats, birds),

                               %% not required, but here for good measure:
                               isoneof(smokes(1), pallmall, prince, blends, bluemaster,  dunhill),
                               isoneof(smokes(2), pallmall, prince, blends, bluemaster,  dunhill),
                               isoneof(smokes(3), pallmall, prince, blends, bluemaster,  dunhill),
                               isoneof(smokes(4), pallmall, prince, blends, bluemaster,  dunhill),
                               isoneof(smokes(5), pallmall, prince, blends, bluemaster,  dunhill),

                               true ].

all_assertions(L) :- assertions(A), basic_assertions(G), append(A, G, L).

declare_enums :-
    z3:z3_declare_enum(pet_enum, [dogs,fish,horses,cats,birds]),
    z3:z3_declare_enum(beverage_enum, [beer, water, milk, coffee, tea]),
    z3:z3_declare_enum(smoke_enum, [pallmall, prince, blends, bluemaster, dunhill] ).

push_assertions(L) :- maplist(z3_push, L).
%% push_assertions(L) :- F =.. [and | L], z3_push(F).

print_model(M) :- print_term(M, [right_margin(10)] ).

assert_puzzle(M) :- all_assertions(All), push_assertions(All), z3_model(M).

doit(M) :- z3:reset_globals, assert_puzzle(M), print_model(M).
doit_enums(M) :- z3:reset_globals, declare_enums, assert_puzzle(M), print_model(M).

implies_test1 :- all_assertions(A), push_assertions(A),
                 z3_is_implied(norwegian = 1 and dane = 2 and brit = 3 and german = 4 and swede = 5).

implies_formula(F) :- all_assertions(A), push_assertions(A), z3_is_implied(F).

house_order(F) :- F = (yellowhouse = 1 and bluehouse = 2 and redhouse = 3 and greenhouse = 4 and whitehouse = 5).
implies_house_order :- house_order(F), implies_formula(F).

%% fails, so house order is implied:
counterexample(F, M) :- all_assertions(A), push_assertions(A), z3_push(not(F)), z3_model(M), print_model(M).
alternate_house_order(M) :- house_order(Order), counterexample(Order, M).

%% pet(3) is getting fish, pet(4) birds,
%% pet order not implied?
pet_order(F) :- F = (pet(1) = cats and pet(2) = horses and pet(3) = birds and pet(4) = fish and pet(5) = dogs).
implies_pet_order :- pet_order(F), implies_formula(F).
alternate_pet_order(M) :- pet_order(Order), counterexample(Order, M).

%% smokes order checks out:
smokes_order(F) :- F = (smokes(1) = dunhill and smokes(2) = blends and smokes(3) = pallmall and smokes(4) = prince and smokes(5) = bluemaster).
implies_smokes_order :- smokes_order(F), implies_formula(F).
alternate_smokes_order(M) :- smokes_order(Order), counterexample(Order, M).

%% drinks order also checks out:
drinks_order(F) :- F = (drinks(1) = water and drinks(2) = tea and drinks(3) = milk and drinks(4) = coffee and drinks(5) = beer).
implies_drinks_order :- drinks_order(F), implies_formula(F).
alternate_drinks_order(M) :- drinks_order(Order), counterexample(Order, M).


%% note that doit(M), doit(M). will fail

:- begin_tests(einstein).

test(no_enums) :-
    z3:reset_globals,
    assert_puzzle(M),
    assertion(member(bluehouse - 2, M.constants)),
    assertion(member(german - 4, M.constants)).

test(enums, [
         setup(z3:z3_reset), cleanup(z3:z3_reset)
     ]) :-
    declare_enums,
    assert_puzzle(M),
    assertion(member(pet(4) - fish, M.functions)).

:- end_tests(einstein).
