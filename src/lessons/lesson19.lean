namespace my_bool

inductive mybool : Type
| mytt : mybool
| myff : mybool

/-
We declare mybool to be an 
inductively defined type:
a value of type, Type. 

The set of values of this 
type that can be constructed 
is defined by the available 
constructors.

Here there are just two, 
mytt and myff, neither having 
any arguments, so these are
the only two values of this 
type: mytt and myff.
-/

-- We open the mybool namespace
open mybool

#check mytt

/-
With this data type in hand,
we can now define an "algebra"
involving such values. This will
be out little implementation of
Boolean algebra. 

First we'll define the unary
functions involving values of
this type only. Then we'll do
a few binary functions, leaving
you a few more as exercises.
-/

/- Unary Operations -/

-- id_mybool returns what it's given
def id_mybool (b: mybool) : mybool := b

-- true_mybool always returns true
def true_mybool (b: mybool) := mytt

-- false_mybool always returns false
def false_mybool (b: mybool) := myff

-- not_mybool returns the other value
def not_mybool : mybool → mybool
| mytt := myff
| myff := mytt

#check not_mybool

def or_mybool : mybool → mybool → mybool
| myff myff := myff
| _ _ := mytt

def and_mybool (b1 b2 : mybool) : mybool :=
match b1, b2 with
    | mytt, mytt := mytt
    | _, _ := myff
end

theorem demorgan1 : ∀ b1 b2 : mybool, 
    not_mybool 
        (and_mybool b1 b2) 
    =
    or_mybool 
        (not_mybool b1) 
        (not_mybool b2) :=
begin
    intros,
    cases b1,
    cases b2,
    repeat {trivial},
end

theorem demorgan2 : ∀ b1 b2 : mybool, 
    not_mybool 
        (or_mybool b1 b2) 
    =
    and_mybool 
        (not_mybool b1) 
        (not_mybool b2) :=
begin
    intros,
    cases b1,
    cases b2,
    repeat {trivial},
    cases b2,
    repeat {trivial},
end



end my_bool