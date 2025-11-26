
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

sig House {
    color: one Color,
    nationality: one Nationality,
    beverage: one Beverage,
    cigar: one Cigar,
    pet: one Pet
}

fact noShared {
    all disj h1, h2: House | {
        h1.color != h2.color
        h1.nationality != h2.nationality
        h1.beverage != h2.beverage
        h1.cigar != h2.cigar
        h1.pet != h2.pet
    }
}

pred isCenterHouse[h: House] {
	h != first && h != last
	h.prev != first && h.next != last
}

pred livesNextTo[h1: House, h2: House] {
	h1.prev = h2 || h1.next = h2
}

fact rules {
    all h: House | {
        h.nationality = brit => h.color = red
        h.nationality = swede => h.pet = dog
        h.nationality = dane => h.beverage = tea
        h.color = green => h.next.color = white
        h.color = green => h.beverage = coffee
        h.cigar = pall => h.pet = bird
        h.color = yellow => h.cigar = dunhill
        isCenterHouse[h] => h.beverage = milk
        h = first => h.nationality = norwegian
        some h2: House | h.cigar = blend => h2.pet = cat && livesNextTo[h, h2]
        some h2: House | h.pet = horse => h2.cigar = dunhill && livesNextTo[h, h2]
        h.cigar = blueMaster => h.beverage = beer
        h.nationality = german => h.cigar = prince
        some h2: House | h.nationality = norwegian => h2.color = blue && livesNextTo[h, h2]
        some h2: House | h.cigar = blend => h2.beverage = water && livesNextTo[h, h2]
    }
}

run {} for 5 but exactly 5 House
