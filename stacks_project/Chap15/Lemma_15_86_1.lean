module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Derived
import StacksCheckRecall

/-!
# Lemma 15.86.1

@stack 0FUY
-/

@[expose] public section

open Algebra
open CategoryTheory ComplexShape DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra NaiveCotangent

universe u

/- Lemma 15.86.1 (1) (0FUY): the canonical derived-to-underived base-change map for
`NL{S⁄R}` has target in degrees `≥ -1` and becomes an isomorphism after applying `τ≥-1`. -/
@[stacks 0FUY "(1), self-presentation underived target concentration"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] =>
  (NaiveCotangent.DerivedBaseChange.selfTargetIsGE (R := R) (S := S) (S' := S') :
    t.IsGE
      (DerivedCategory.Q.obj
        ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
          ((Algebra.naiveCotangent R S).extend embeddingDownNat))) (-1))

@[stacks 0FUY "(1), self-presentation base-change comparison"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] =>
  (NaiveCotangent.DerivedBaseChange.selfComparison (R := R) (S := S) (S' := S') :
    (ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
        (Algebra.naiveCotangentObject R S) ⟶
      DerivedCategory.Q.obj
        ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
          ((Algebra.naiveCotangent R S).extend embeddingDownNat)))

@[stacks 0FUY "(1), self-presentation truncation comparison"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] =>
  (NaiveCotangent.DerivedBaseChange.selfTruncGEComparison (R := R) (S := S) (S' := S') :
    (t.truncGE (-1)).obj
        ((ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
          (Algebra.naiveCotangentObject R S)) ⟶
      (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
            ((Algebra.naiveCotangent R S).extend embeddingDownNat))))

@[stacks 0FUY "(1), self-presentation truncation isomorphism"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] =>
  (NaiveCotangent.DerivedBaseChange.selfTruncGEComparison_isIso
      (R := R) (S := S) (S' := S') :
    IsIso (NaiveCotangent.DerivedBaseChange.selfTruncGEComparison
      (R := R) (S := S) (S' := S')))

/- Lemma 15.86.1 (2) (0FUY): the same target concentration and truncation-isomorphism statement
holds for the naive cotangent complex of every chosen presentation. -/
@[stacks 0FUY "(2), presentation underived target concentration"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] {ι κ : Type u} (P : Presentation R S ι κ) =>
  (NaiveCotangent.DerivedBaseChange.presentationTargetIsGE (S' := S') P :
    t.IsGE
      (DerivedCategory.Q.obj
        ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat))) (-1))

@[stacks 0FUY "(2), presentation base-change comparison"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] {ι κ : Type u} (P : Presentation R S ι κ) =>
  (NaiveCotangent.DerivedBaseChange.presentationComparison (S' := S') P :
    (ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
        (DerivedCategory.Q.obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat)) ⟶
      DerivedCategory.Q.obj
        ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat)))

@[stacks 0FUY "(2), presentation truncation comparison"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] {ι κ : Type u} (P : Presentation R S ι κ) =>
  (NaiveCotangent.DerivedBaseChange.presentationTruncGEComparison (S' := S') P :
    (t.truncGE (-1)).obj
        ((ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
          (DerivedCategory.Q.obj
            ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat))) ⟶
      (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((NaiveCotangent.DerivedBaseChange.scalarExtendedCochain (algebraMap S S')).obj
            ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat))))

@[stacks 0FUY "(2), presentation truncation isomorphism"]
#check fun {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] {ι κ : Type u} (P : Presentation R S ι κ) =>
  (NaiveCotangent.DerivedBaseChange.presentationTruncGEComparison_isIso (S' := S') P :
    IsIso (NaiveCotangent.DerivedBaseChange.presentationTruncGEComparison (S' := S') P))

end
