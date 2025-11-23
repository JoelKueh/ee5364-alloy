
open util/ordering[House]

abstract sig Color {}
one sig red, green, white, yellow, blue extends Color {}
abstract sig Nationality {}
one sig brit, swede, dane, norwegian, german extends Nationality {}
abstract sig Beverage {}
one sig tea, coffee, milk, beer, water extends Beverage {}
abstract sig Cigar {}
one sig pall, dunhill, blend, blueMaster, prince extends Cigar {}
abstract sig Pet {}
one sig dog, bird, cat, horse, fish extends Pet {}

sig Person {
	house: one House,
	nationality: one Nationality,
	beverage: one Beverage,
	cigar: one Cigar,
	pet: one Pet
}

sig House {
	color: one Color,
	person: one Person
}

fact noShared {
	all disj p1, p2: Person |
		p1.house not in p2.house &&
		p1.nationality not in p2.nationality &&
		p1.beverage not in p2.beverage &&
		p1.cigar not in p2.cigar &&
		p1.pet not in p2.pet
	all disj h1, h2: House |
		h1.color not in h2.color
}

pred houseHasPerson {
	all p: Person, h: House | p.house = h => h.person = p
}

pred isCenterHouse[h: House] {
	h != first && h != last
	h.prev != first && h.next != last
}

pred livesNextTo[p1: Person, p2: Person] {
	p1.house.prev.person = p2 || p1.house.next.person = p2
}

fact rules {
	all p: Person | p.nationality = brit => p.house.color = red
	all p: Person | p.nationality = swede => p.pet = dog
	all p: Person | p.nationality = dane => p.beverage = tea
	all h: House | h.color = green => h.next.color = white
	all p: Person | p.house.color = green => p.beverage = coffee
	all p: Person | p.cigar = pall => p.pet = bird
	all p: Person | p.house.color = yellow => p.cigar = dunhill
	all p: Person | isCenterHouse[p.house] => p.beverage = milk
	all p: Person | p.nationality = norwegian => p.house = first
	all p1: Person | some p2: Person | p1.cigar = blend => p2.pet = cat && livesNextTo[p1, p2]
	all p1: Person | some p2: Person | p1.pet = horse => p2.cigar = dunhill && livesNextTo[p1, p2]
	all p: Person | p.beverage = beer => p.cigar = blueMaster
	all p: Person | p.nationality = german => p.cigar = prince
	all p1: Person | some p2: Person | p1.nationality = norwegian => p2.house.color = blue && livesNextTo[p1, p2]
	all p1: Person | some p2: Person | p1.cigar = blend => p2.beverage = water && livesNextTo[p1, p2]
}

run {} for 5 but exactly 5 Person
