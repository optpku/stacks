/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Presentation

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

/-
Domain-style sampling for Proposition 7.44.3:
- primary domain: morphisms of topoi and the induced inverse-image and direct-image functors on
  sheaves of
  algebraic structures;
- sampled owner API:
  `MorphismOfTopoiIn.Presentation.directImageIso`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPushforwardContinuous.compSheafCompose`,
  `Functor.sheafPullback.compSheafComposeIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks comparison between a presented morphism of topoi and the induced
  inverse-image and direct-image functors on sheaves of algebraic structures;
  `core/canonical`: the topoi-presentation comparison isomorphisms from `Remark_7_15_4` and the
  coefficient-functor compatibility owners from ReasLib;
  `bridge/view`: the two whiskered comparison expressions below.

Primitive data are only the morphism-of-sites presentation and the algebraic-structure owner
`IsAlgebraicStructure A (forget A)`. The comparison isomorphisms are derived bridge API, so this
file should recall the upstream owners directly and keep only the thin whiskered comparison
expressions below.
-/

section MorphismOfTopoi

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: for a morphism of topoi `f : Sh(K) ⟶ Sh(J)`, the canonical presentation
`U ↦ f⁻¹(h_U^#)` from the ReasLib presentation API recovers the original direct-image functor on underlying
sheaves of sets. -/
@[stacks 00YV] #check @MorphismOfTopoiIn.Presentation.directImageIso

end MorphismOfTopoi

section AlgebraicStructures

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Proposition 7.44.3: the additional Stacks examples of sheaves of algebraic structures are
obtained by applying the general sheaf-theoretic constructions to the standard algebraic-structure
categories already recorded in Lemma 6.15.2. The listed categories are therefore reused directly,
rather than repackaged into a new conjunction theorem. -/
#check @pointedAlgebraicStructure
#check @addCommGrpCatAlgebraicStructure
#check @grpCatAlgebraicStructure
#check @monCatAlgebraicStructure
#check @commRingCatAlgebraicStructure
#check @moduleCatAlgebraicStructureOfCommRing
#check @lieAlgebraCatAlgebraicStructureOfField

variable (A : Type w) [Category.{max u₁ u₂ v} A]
variable {FA : A → A → Type (max u₁ u₂ v)} {CA : A → Type (max u₁ u₂ v)}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable [IsAlgebraicStructure A (forget A)]
variable (u : C ⥤ D)

variable [IsMorphismOfSites J K u]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K A]

/- Proposition 7.44.3: on sheaves of algebraic structures, the induced inverse-image and
direct-image functors are the canonical adjoint pair `u.sheafPullback A J K ⊣
u.sheafPushforwardContinuous A J K`. -/
#check @Functor.sheafAdjunctionContinuous

variable [J.HasSheafCompose (forget A)] [K.HasSheafCompose (forget A)]
variable {f : MorphismOfTopoiIn J K}
variable (ePush : u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K ≅ f.pushforward)

/- Proposition 7.44.3: if the direct-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced direct image on sheaves of `A`-valued algebraic structures forgets to the direct
image of `f`; this is the generic coefficient comparison specialized to `forget A`, whiskered with
the presentation isomorphism `ePush`. -/
#check
  (eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose u (forget A) J K) ≪≫
      (sheafCompose K (forget A)).isoWhiskerLeft ePush :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J (forget A) ≅
      sheafCompose K (forget A) ⋙ f.pushforward)

/- Proposition 7.44.3: the induced direct-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
#check @Functor.sheafPushforwardContinuous.compSheafCompose

variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]
variable [HasWeakSheafify K (Type (max u₁ u₂ v))]
variable [K.PreservesSheafification (forget A)]
variable (eInv : u.sheafPullback (Type (max u₁ u₂ v)) J K ≅ f⁻¹)

/- Proposition 7.44.3: if the inverse-image functor of a morphism of topoi
`f : Sh(K) ⟶ Sh(J)` is presented on underlying sheaves of sets by the continuous functor `u`,
then the induced inverse image on sheaves of `A`-valued algebraic structures forgets to the
inverse image of `f`; this is the generic coefficient comparison specialized to `forget A`,
whiskered with the presentation isomorphism `eInv`. -/
#check
  (Functor.sheafPullback.compSheafComposeIso u (forget A) J K ≪≫
      (sheafCompose J (forget A)).isoWhiskerLeft eInv :
    u.sheafPullback A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙ f⁻¹)

/- Proposition 7.44.3: the induced inverse-image functor on sheaves of algebraic structures
commutes with forgetting to sheaves of sets. -/
#check @Functor.sheafPullback.compSheafComposeIso

end AlgebraicStructures

end CategoryTheory
