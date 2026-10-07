module

public import ReasLib.RingTheory.RingHom.IndZariski.Composition
import StacksCheckRecall

@[expose] public section

universe u v w uA uB uC

/- Lemma 61.4.4: if `B → C` is an `A`-algebra homomorphism and `A → B` and
`A → C` are ind-Zariski, then `B → C` is ind-Zariski. -/
@[stacks 096R] #check (RingHom.IndZariski.of_over_common_base :
  ∀ {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B],
    (algebraMap R A).IndZariski → (algebraMap R B).IndZariski →
      (algebraMap A B).IndZariski)

#check (RingHom.IndZariski.Raw.of_over_common_base :
  ∀ {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B],
    RingHom.IndZariski.Raw.{u, v, uA} (algebraMap R A) →
    RingHom.IndZariski.Raw.{u, w, uB} (algebraMap R B) →
      RingHom.IndZariski.Raw.{v, w, uC} (algebraMap A B))
