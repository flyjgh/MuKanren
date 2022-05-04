include("../src/core.jl")

assp(==(0),((0,1), (1,:cat)))
assp(==(1),((0,1), (1,:cat)))
assp(==(2),((0,1), (:fish,:cat)))
assp(==(1),((1,:cat)))
assp(==(2),((1,:cat)))

walk(5, ((3,:cat)))
walk(0, ((3,:cat), (2,4), (1,2), (0,1)))
walk(0, ((3,:cat), (2,3), (1,2), (0,1)))
walk(1,(0,1))
walk(3,(0,1))
walk(0,((0, (2, 4)), (1, 3)))
walk(5,((0, (2, 4)), (1, 3)))

occurs(1,0,(0, 1))
occurs(0,1,(0, 1))
occurs(0, (2, 4), ((:cat, :fish), (0, 1)))
occurs(1, (1, :cat), ((2, 1),))
occurs(3, (2, 4), (1, 3))

ext_s(1, (1, 0), ((0, 1)))
ext_s(0, (:dog, :cat), ((1, 3)))
ext_s(0, 2, ((1, 3)))

unify((0,1),(1,:cat),())
unify((0,1),(0,:cat),())
unify((0,1),(0,:cat),(2,3))
un=unify(((0,1),2),((1,:cat),3),())
walk(0,un)
walk(2,un)

((0,1) ≣ (1,:cat))(((),2))
((0,1) ≣ (0,:cat))(((),2))
(((:cat,0),1) ≣ ((:cat,:horse),:turtle))(((),2))

((((:cat,0),1) ≣ ((:cat,:horse),:turtle)) ∨ ((:cat, :fish) ≣ 0))(((),2))
((((:cat,0),1) ≣ ((:cat,:horse),:turtle)) ∧ ((:cat, :fish) ≣ 0))(((),2))

turtles(x) = state -> () -> ((x ≣ :turtle) ∨ turtles(x))(state)
turtles(5)(((),1))()
