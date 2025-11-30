// 🧩 Alloy Model for the Zebra Puzzle (Einstein's Riddle)

// --- Signatures ---

// Define the 5 positions (H1 through H5) as extensions of the House signature.
sig House {
    nationality: one Nationality,
    color: one Color,
    beverage: one Beverage,
    cigar: one Cigar,
    pet: one Pet
}

// Explicitly name the 5 houses to enforce a total ordering for positional logic.
one sig H1, H2, H3, H4, H5 extends House {}

// Define the categories of characteristics using 'enum' for clarity.
enum Nationality { Brit, Swede, Dane, Norwegian, German }
enum Color { Red, Green, White, Yellow, Blue }
enum Beverage { Tea, Coffee, Milk, Beer, Water }
enum Cigar { PallMall, Dunhill, Blends, BlueMaster, Prince }
enum Pet { Dogs, Birds, Cats, Horses, Fish }


// --- Ordering and Positional Logic ---

// Function to get the house immediately to the right.
fun right [h: House]: lone House {
    (h = H1) => H2 else (
    (h = H2) => H3 else (
    (h = H3) => H4 else (
    (h = H4) => H5 else none)))
}

// Predicate for houses being immediate neighbors.
pred next_to [h1, h2: House] {
    h2 = right[h1] or h1 = right[h2]
}


// --- Core Facts (Global Constraints) ---

// 1. Enforce a one-to-one mapping: each house has a unique set of characteristics.
fact UniqueProperties {
    all c: Color | one h: House | h.color = c
    all n: Nationality | one h: House | h.nationality = n
    all b: Beverage | one h: House | h.beverage = b
    all ci: Cigar | one h: House | h.cigar = ci
    all p: Pet | one h: House | h.pet = p
}

// 2. Enforce all the riddle hints.
fact Constraints {
    // 1. The Brit lives in the red house
    some h: House | h.nationality = Brit and h.color = Red

    // 2. The Swede keeps dogs as pets
    some h: House | h.nationality = Swede and h.pet = Dogs

    // 3. The Dane drinks tea
    some h: House | h.nationality = Dane and h.beverage = Tea

    // 4. The green house is on the left of the white house
    some h_green: House | h_green.color = Green and right[h_green].color = White

    // 5. The green house’s owner drinks coffee
    some h: House | h.color = Green and h.beverage = Coffee

    // 6. The person who smokes Pall Mall rears birds
    some h: House | h.cigar = PallMall and h.pet = Birds

    // 7. The owner of the yellow house smokes Dunhill
    some h: House | h.color = Yellow and h.cigar = Dunhill

    // 8. The man living in the center house (H3) drinks milk
    H3.beverage = Milk

    // 9. The Norwegian lives in the first house (H1)
    H1.nationality = Norwegian

    // 10. The man who smokes blends lives next to the one who keeps cats
    some h_blend, h_cats: House | h_blend.cigar = Blends and h_cats.pet = Cats and next_to[h_blend, h_cats]

    // 11. The man who keeps horses lives next to the man who smokes Dunhill
    some h_horses, h_dunhill: House | h_horses.pet = Horses and h_dunhill.cigar = Dunhill and next_to[h_horses, h_dunhill]

    // 12. The Owner who smokes BlueMaster drinks beer
    some h: House | h.cigar = BlueMaster and h.beverage = Beer

    // 13. The German smokes Prince
    some h: House | h.nationality = German and h.cigar = Prince

    // 14. The Norwegian lives next to the blue house
    some h_norwegian, h_blue: House | h_norwegian.nationality = Norwegian and h_blue.color = Blue and next_to[h_norwegian, h_blue]

    // 15. The man who smokes blend has a neighbor who drinks water
    some h_blend, h_water: House | h_blend.cigar = Blends and h_water.beverage = Water and next_to[h_blend, h_water]
}


// --- Solving Predicate and Run Command ---

// The predicate simply verifies that an instance satisfying all facts exists.
pred solve {}

// Execute the model: find a single solution instance that satisfies all facts.
// The Analyzer will try to find a solution (an instance) for exactly 5 House atoms.
run solve for exactly 5 House
