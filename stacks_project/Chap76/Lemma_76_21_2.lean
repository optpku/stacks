module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.EtaleLocalization
import StacksCheckRecall

/-!
# Étale localization of the naive cotangent complex of algebraic spaces

A commutative square of algebraic spaces over a scheme `S` with étale vertical arrows
yields a canonical identification of naive cotangent complexes in `D(𝒪_U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open AlgebraicGeometry.AlgebraicSpace.Modules
open ComplexShape
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.21.2: Let `S` be a scheme. Consider a commutative diagram of algebraic spaces
over `S` with étale vertical arrows `p : U ⟶ X` and `q : V ⟶ Y`. Then there is a canonical
identification `NL[f]|_{U_étale} = NL[g]` in `D(𝒪_U)`. -/
@[stacks 0D0W] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.etaleRestrictIso_derived :
    ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
      (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
      [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q),
      DerivedCategory.Q.obj
          (((Modules.restrictFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (Hom.naiveCotangent f)) ≅
        DerivedCategory.Q.obj (Hom.naiveCotangent g))
