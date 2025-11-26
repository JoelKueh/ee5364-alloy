
// Einstein's riddle — Alloy 6.2.0 compatible
open util/ordering[House]

/* Attribute sets (exactly these 5 of each) */
abstract sig Color {}
one sig Red, Green, White, Yellow, Blue extends Color {}

abstract sig Nationality {}
one sig Brit, Swede, Dane, Norwegian, German extends Nationality {}

abstract sig Pet {}
one sig Dog, Bird, Cat, Horse, Fish extends Pet {}

abstract sig Drink {}
one sig Tea, Coffee, Milk, Beer, Water extends Drink {}

abstract sig Smoke {}
one sig PallMall, Dunhill, Blend, BlueMaster, Prince extends Smoke {}

/* Houses */
sig House {
  color: one Color,
  nat:   one Nationality,
  pet:   one Pet,
  drink: one Drink,
  smoke: one Smoke
}

/* Force exactly five houses (safety net to avoid wrong run scopes) */
fact exactlyFiveHouses { #House = 5 }

/* Enforce bijections: each attribute value appears in exactly one house */
fact bijections {
  all c: Color | one h: House | h.color = c
  all n: Nationality | one h: House | h.nat = n
  all p: Pet | one h: House | h.pet = p
  all d: Drink | one h: House | h.drink = d
  all s: Smoke | one h: House | h.smoke = s
}

/* adjacency/ordering helper predicates */
pred immediatelyLeft(a, b: House) { next[a] = b }
pred leftOf(a, b: House) { b in a.^next }
pred adjacent(a, b: House) { next[a] = b or next[b] = a }

/* Clues encoded as facts (using next[...] to avoid parser pitfalls) */
fact clues {
  some h: House | h.nat = Brit and h.color = Red
  some h: House | h.nat = Swede and h.pet = Dog
  some h: House | h.nat = Dane and h.drink = Tea
  some g, w: House | g.color = Green and w.color = White and next[g] = w
  some h: House | h.color = Green and h.drink = Coffee
  some h: House | h.smoke = PallMall and h.pet = Bird
  some h: House | h.color = Yellow and h.smoke = Dunhill
  first.next.next.drink = Milk
  first.nat = Norwegian
  some a, b: House | a.smoke = Blend and b.pet = Cat and (next[a] = b or next[b] = a)
  some a, b: House | a.pet = Horse and b.smoke = Dunhill and (next[a] = b or next[b] = a)
  some h: House | h.smoke = BlueMaster and h.drink = Beer
  some h: House | h.nat = German and h.smoke = Prince
  some b: House | b.color = Blue and (next[first] = b or next[b] = first)
  some a, b: House | a.smoke = Blend and b.drink = Water and (next[a] = b or next[b] = a)
}

/* Top-level predicate to produce a full solution */
pred showSolution {}
fact useShow { showSolution }

run showSolution for exactly 5 House,
                     exactly 5 Color, exactly 5 Nationality, exactly 5 Pet, exactly 5 Drink, exactly 5 Smoke

