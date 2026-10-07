module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Degenerate
public import ReasLib.CategoryTheory.NatTrans.Arrow

/-!
# Normalized cochain complexes of cosimplicial objects

The source-facing normalized cochain complex is the cokernel of the degenerate inclusion.  The
transported normalized Moore complex supplies a comparison model and the resulting Dold--Kan
equivalence, but is not used to replace the quotient definition.

@stack 019I
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

section Complement

variable [Preadditive A] [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]

namespace normalizedCochainComplex

/-- The complementary endomorphism of the alternating coface complex determined by the split
source-facing degenerate summand. -/
@[stacks 019I "normalized quotient complementary projector"]
def complement (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ (alternatingCofaceMapComplex A).obj U :=
  𝟙 _ - degenerateCochainComplex.ρ U ≫ degenerateCochainComplex.ι U

/-- The complementary endomorphism annihilates the source-facing degenerate inclusion. -/
@[reassoc, stacks 019I "normalized quotient complementary projector annihilates degeneracies"]
theorem degenerate_ι_comp_complement (U : CosimplicialObject A) :
    degenerateCochainComplex.ι U ≫ complement U = 0 := sorry

/-- The complementary normalized projector is idempotent. -/
@[reassoc, stacks 019I "normalized quotient complementary projector idempotence"]
theorem complement_comp_complement (U : CosimplicialObject A) :
    complement U ≫ complement U = complement U := sorry

end normalizedCochainComplex

end Complement

section Quotient

variable [Preadditive A] [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]
  [hC : HasCokernels (CochainComplex A ℕ)]

/-- The normalized cochain complex functor, defined as the cokernel of the
degenerate inclusion. -/
@[stacks 019I "normalized cochain complex functor"]
abbrev normalizedCochainComplex.functor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  (degenerateCochainComplex.ι.natTrans (A := A)).arrowFunctor ⋙
    Limits.coker (CochainComplex A ℕ)

/-- The normalized cochain complex of a cosimplicial object. -/
@[stacks 019I "normalized cochain complex"]
abbrev normalizedCochainComplex (U : CosimplicialObject A) : CochainComplex A ℕ :=
  normalizedCochainComplex.functor.obj U

namespace normalizedCochainComplex

/-- The canonical quotient map from the alternating coface complex to the normalized cochain
complex. -/
@[stacks 019I "normalized cochain quotient map"]
def π (U : CosimplicialObject A) :
    (alternatingCofaceMapComplex A).obj U ⟶ normalizedCochainComplex U :=
  cokernel.π (degenerateCochainComplex.ι U)

/-- The normalized-cochain quotient map is an epimorphism. -/
@[stacks 019I "normalized cochain quotient epimorphism"]
instance π_epi (U : CosimplicialObject A) : Epi (π U) := sorry

/-- The degenerate inclusion is annihilated by the normalized-cochain quotient. -/
@[reassoc, stacks 019I "normalized quotient annihilates degenerate cochains"]
theorem degenerate_ι_comp_π (U : CosimplicialObject A) :
    degenerateCochainComplex.ι U ≫ π U = 0 := sorry

/-- Descend a morphism out of alternating cochains through the normalized quotient. -/
@[stacks 019I "normalized cochain quotient descent"]
def desc (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    (f : (alternatingCofaceMapComplex A).obj U ⟶ K)
    (h : degenerateCochainComplex.ι U ≫ f = 0) :
    normalizedCochainComplex U ⟶ K :=
  cokernel.desc (degenerateCochainComplex.ι U) f h

/-- A morphism descended through normalized cochains recovers its defining morphism after the
quotient map. -/
@[reassoc, stacks 019I "normalized cochain quotient descent formula"]
theorem π_desc (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    (f : (alternatingCofaceMapComplex A).obj U ⟶ K)
    (h : degenerateCochainComplex.ι U ≫ f = 0) :
    π U ≫ desc U f h = f := sorry

/-- Morphisms out of normalized cochains are determined after precomposition with the quotient
map. -/
@[ext, stacks 019I "normalized cochain quotient hom extensionality"]
theorem hom_ext (U : CosimplicialObject A) {K : CochainComplex A ℕ}
    {f g : normalizedCochainComplex U ⟶ K} (h : π U ≫ f = π U ≫ g) : f = g := sorry

/- The inclusion API below belongs to the quotient itself; it does not depend on a Moore model. -/

/-- The canonical inclusion of the source-facing normalized quotient, obtained from its
complementary projector. -/
@[stacks 019I "normalized quotient canonical section"]
noncomputable def ι (U : CosimplicialObject A) :
    normalizedCochainComplex U ⟶ (alternatingCofaceMapComplex A).obj U :=
  desc U (complement U) (degenerate_ι_comp_complement U)

/-- The quotient followed by the canonical inclusion is the complementary projector. -/
@[reassoc, stacks 019I "normalized quotient section projector formula"]
theorem π_comp_ι (U : CosimplicialObject A) :
    π U ≫ ι U = complement U := sorry

/-- The complementary normalized projector is unchanged after postcomposition with the quotient.
-/
@[reassoc, stacks 019I "normalized quotient complementary projector quotient formula"]
theorem complement_comp_π (U : CosimplicialObject A) :
    complement U ≫ π U = π U := sorry

/-- The canonical normalized inclusion is a right inverse of the quotient map. -/
@[reassoc, stacks 019I "normalized quotient section retract law"]
theorem ι_comp_π (U : CosimplicialObject A) :
    ι U ≫ π U = 𝟙 (normalizedCochainComplex U) := sorry

/-- Naturality of the canonical quotient map to normalized cochains. -/
@[reassoc, stacks 019I "normalized cochain quotient naturality"]
theorem π.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ π V =
      π U ≫ normalizedCochainComplex.functor.map f := sorry

/-- The quotient maps form the canonical natural transformation from alternating to normalized
cochains. -/
@[stacks 019I "normalized cochain quotient"]
def π.natTrans : alternatingCofaceMapComplex A ⟶ normalizedCochainComplex.functor where
  app U := π U
  naturality _ _ f := π.naturality f

/-- The normalized quotient natural transformation has component `π U` at `U`. -/
@[simp, stacks 019I "normalized cochain quotient natural transformation component"]
theorem π.natTrans.app (U : CosimplicialObject A) :
    (π.natTrans (A := A)).app U = π U := sorry

/-- Naturality of the canonical source-facing normalized quotient inclusion. -/
@[reassoc, stacks 019I "normalized quotient section naturality"]
theorem ι.naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplex.functor.map f ≫ ι V =
      ι U ≫ (alternatingCofaceMapComplex A).map f := sorry

/-- The canonical source-facing normalized quotient inclusions form a natural transformation. -/
@[stacks 019I "normalized quotient section natural transformation"]
noncomputable def ι.natTrans :
    normalizedCochainComplex.functor ⟶ alternatingCofaceMapComplex A where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The component of the source-facing normalized quotient inclusion natural transformation. -/
@[simp, stacks 019I "normalized quotient section natural transformation component"]
theorem ι.natTrans.app (U : CosimplicialObject A) :
    (ι.natTrans (A := A)).app U = ι U := sorry

/-- The source-facing normalized quotient inclusion and quotient form a natural retract. -/
@[reassoc, stacks 019I "normalized quotient section natural retract law"]
theorem ι.natTrans_comp_π :
    ι.natTrans (A := A) ≫ π.natTrans (A := A) =
      𝟙 (normalizedCochainComplex.functor (A := A)) := sorry

namespace ι

/-- A normalized inclusion component, equipped with its quotient retraction. -/
@[stacks 019I "normalized cochain component split monomorphism"]
noncomputable def appSplitMono (U : CosimplicialObject A) : SplitMono (ι U) where
  retraction := π U
  id := ι_comp_π U

/-- Every normalized inclusion component is canonically split. -/
@[instance, stacks 019I "normalized cochain component split monomorphism instance"]
theorem appIsSplitMono (U : CosimplicialObject A) : IsSplitMono (ι U) := sorry

/-- The natural normalized inclusion, equipped with its quotient retraction. -/
@[stacks 019I "normalized cochain natural split monomorphism"]
noncomputable def splitMono : SplitMono (natTrans (A := A)) where
  retraction := π.natTrans (A := A)
  id := normalizedCochainComplex.ι.natTrans_comp_π (A := A)

/-- The natural normalized inclusion is canonically split. -/
@[instance, stacks 019I "normalized cochain natural split monomorphism instance"]
theorem isSplitMono : IsSplitMono (natTrans (A := A)) := sorry

end ι

namespace π

/-- A normalized quotient component, equipped with its canonical section. -/
@[stacks 019I "normalized cochain component split epimorphism"]
noncomputable def appSplitEpi (U : CosimplicialObject A) : SplitEpi (π U) where
  section_ := ι U
  id := ι_comp_π U

/-- Every normalized quotient component is canonically split. -/
@[instance, stacks 019I "normalized cochain component split epimorphism instance"]
theorem appIsSplitEpi (U : CosimplicialObject A) : IsSplitEpi (π U) := sorry

/-- The natural normalized quotient, equipped with its canonical section. -/
@[stacks 019I "normalized cochain natural split epimorphism"]
noncomputable def splitEpi : SplitEpi (natTrans (A := A)) where
  section_ := ι.natTrans (A := A)
  id := normalizedCochainComplex.ι.natTrans_comp_π (A := A)

/-- The natural normalized quotient is canonically split. -/
@[instance, stacks 019I "normalized cochain natural split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (natTrans (A := A)) := sorry

end π

end normalizedCochainComplex

end Quotient

end CategoryTheory.CosimplicialObject
