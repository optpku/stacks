module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality
public import stacks_project.Chap66.Lemma_66_12_2_Invariant

/-!
# Atlas pullback and restricted quotient for invariant immersions

The correspondence between locally closed subspaces of the fppf quotient sheaf `U / R` and
`R`-invariant immersions into `U` is realized by pulling back along the canonical quotient map
and by forming the quotient sheaf of the restricted relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- A locally closed subspace of the associated algebraic space `X = U / R` is an fppf sheaf
over `S` together with a sheaf morphism to `P.quotientSheaf (Scheme.fppfTopology.over S)` that
is a relative immersion with respect to `uliftYoneda`. -/
structure LocallyClosedSubspace {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] where
  /-- The fppf sheaf underlying the locally closed subspace. -/
  X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  /-- The inclusion of the subspace into `U / R`. -/
  ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S)
  /-- The inclusion is a relative immersion with respect to `uliftYoneda`. -/
  isImmersion :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom

namespace LocallyClosedSubspace

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The locally closed subspace of `U / R` determined by a relative immersion into the
fppf quotient sheaf of `P`. -/
def ofι {X : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (ι : X ⟶ P.quotientSheaf (Scheme.fppfTopology.over S))
    (h : (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} ι.hom) :
    LocallyClosedSubspace P where
  X := X
  ι := ι
  isImmersion := h

/-- The inclusion of a locally closed subspace is a relative immersion, hence a monomorphism
of underlying presheaves. -/
theorem spec (Z : LocallyClosedSubspace P) :
    (over (@AlgebraicGeometry.IsImmersion)).relative uliftYoneda.{u + 1} Z.ι.hom ∧
      Mono Z.ι.hom := sorry

/-- A relative immersion of fppf sheaves is a monomorphism of underlying presheaves. -/
theorem mono_hom (Z : LocallyClosedSubspace P) : Mono Z.ι.hom := sorry

/-- The subobject of the underlying presheaf of `U / R` represented by a locally closed
subspace. -/
def subobject (Z : LocallyClosedSubspace P) :
    Subobject (P.quotientSheaf (Scheme.fppfTopology.over S)).obj :=
  @Subobject.mk _ _ _ _ Z.ι.hom (mono_hom Z)

/-- The subobject of a locally closed subspace is `Subobject.mk` of the underlying presheaf
morphism of its inclusion. -/
theorem subobject_eq_mk (Z : LocallyClosedSubspace P) :
    Z.subobject = @Subobject.mk _ _ _ _ Z.ι.hom (mono_hom Z) := sorry

/-- The `R`-invariant immersion `Z ×_X U ⟶ U` obtained by taking the `uliftYoneda`-represented
pullback of the sheaf inclusion along the canonical quotient map. -/
def pullbackAlong (Z : LocallyClosedSubspace P) : InvariantImmersion P where
  Z := Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom
  ι := Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isImmersion := Z.isImmersion.property_snd (P.quotientMap (Scheme.fppfTopology.over S)).hom
  isInvariant := sorry

/-- The underlying scheme of `pullbackAlong Z` is the `uliftYoneda`-represented fibre product of
the sheaf inclusion with the quotient map. -/
theorem pullbackAlong_Z (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).Z =
      Z.isImmersion.rep.pullback (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

/-- The inclusion of `pullbackAlong Z` is the represented pullback projection of the sheaf
inclusion along the quotient map. -/
theorem pullbackAlong_ι (Z : LocallyClosedSubspace P) :
    (pullbackAlong Z).ι =
      Z.isImmersion.rep.snd (P.quotientMap (Scheme.fppfTopology.over S)).hom := sorry

end LocallyClosedSubspace

namespace InvariantImmersion

open LocallyClosedSubspace

variable {S : Scheme.{u}} {U : Over S} {P : PreRelation U} [P.IsEtaleEquivalenceRelation]

/-- The locally closed subspace `Z' / R'` of `U / R` associated with an `R`-invariant immersion,
obtained as the fppf quotient sheaf of the restricted relation. -/
def toLocallyClosedSubspace (Z' : InvariantImmersion P) : LocallyClosedSubspace P where
  X := (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S)
  ι := (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S)
  isImmersion := sorry

/-- The underlying sheaf of `toLocallyClosedSubspace Z'` is the fppf quotient sheaf of the
restricted relation. -/
theorem toLocallyClosedSubspace_X (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').X =
      (P.pullback Z'.ι).quotientSheaf (Scheme.fppfTopology.over S) := sorry

/-- The inclusion of `toLocallyClosedSubspace Z'` is `quotientSheafMap` of the canonical
pullback morphism of relations. -/
theorem toLocallyClosedSubspace_ι (Z' : InvariantImmersion P) :
    (toLocallyClosedSubspace Z').ι =
      (P.pullbackHom Z'.ι).quotientSheafMap (Scheme.fppfTopology.over S) := sorry

/-- The quotient of an invariant immersion is a relative closed immersion if and only if the
immersion into `U` is a closed immersion of schemes. -/
theorem isClosedImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsClosedImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsClosedImmersion Z'.ι.left := sorry

/-- The quotient of an invariant immersion is a relative open immersion if and only if the
immersion into `U` is an open immersion of schemes. -/
theorem isOpenImmersion_toLocallyClosedSubspace_iff (Z' : InvariantImmersion P) :
    (over (@AlgebraicGeometry.IsOpenImmersion)).relative uliftYoneda.{u + 1}
        (toLocallyClosedSubspace Z').ι.hom ↔
      AlgebraicGeometry.IsOpenImmersion Z'.ι.left := sorry

end InvariantImmersion

end AlgebraicGeometry.Scheme.PreRelation
