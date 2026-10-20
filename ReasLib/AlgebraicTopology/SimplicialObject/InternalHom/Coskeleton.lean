/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Zero
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Coskeleton
public import Mathlib.CategoryTheory.CommSq

/-!
# Coskeletons and simplicial internal homs

Restriction to the first `n` simplicial degrees converts maps into an objectwise `n`-coskeleton
from a constant copower indexed by `K` into maps from the copower indexed by `sk n K`.  This
equivalence is natural in the constant object, hence packages as an isomorphism of presheaves.
When `K = Δ[q]`, standard-simplex evaluation says that degree `q` of the coskeleton represents
the corresponding constant-object mapping presheaf.

The arbitrary-index copower equivalence is the root API.  The degreewise representability and
the comparison with degree zero of an internal mapping object are its representable-simplex
specializations.  None of these declarations requires coskeletons for unrelated truncated
simplicial objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.internalHom.coskeleton

variable {C : Type u} [Category.{v} C]

namespace rightKan

section ConstantRestriction

variable (n : ℕ) (K : SSet.{w}) (V : SimplicialObject C) {W : SimplicialObject C}
variable (ε : (SimplexCategory.Truncated.inclusion n).op ⋙ W ⟶ (truncation n).obj V)
variable [W.IsRightKanExtension ε]
variable [HasConstCopowers K C]
variable [HasConstCopowers ((SSet.sk n).obj K) C]

/-- The component at a constant object of the presheaf comparison induced by an explicit right
Kan presentation. -/
@[stacks 018V "right-Kan constant-restriction component"]
noncomputable def constRestrictionIso.app (X : Cᵒᵖ) :
    (constRestriction K W).obj X ≅
      (constRestriction ((SSet.sk n).obj K) V).obj X :=
  Equiv.toIso (copower.truncation.rightKanHomEquiv n K V ε X.unop)

/-- The components of the constant-restriction comparison for a right Kan presentation are
natural in the test object. -/
@[stacks 018V "right-Kan constant-restriction naturality"]
theorem constRestrictionIso.naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (constRestriction K W).map f ≫
        (constRestrictionIso.app n K V ε Y).hom =
      (constRestrictionIso.app n K V ε X).hom ≫
        (constRestriction ((SSet.sk n).obj K) V).map f := sorry

/-- An explicit right Kan presentation identifies the corresponding constant-object mapping
presheaf with the one indexed by the simplicial-set skeleton. -/
@[stacks 018V "right-Kan constant-restriction comparison"]
noncomputable def constRestrictionIso :
    constRestriction K W ≅ constRestriction ((SSet.sk n).obj K) V :=
  NatIso.ofComponents (constRestrictionIso.app n K V ε)
    (constRestrictionIso.naturality n K V ε)

end ConstantRestriction

end rightKan

section ConstantRestriction

variable (n : ℕ) (K : SSet.{w}) (V : SimplicialObject C)
variable [HasConstCopowers K C]
variable [HasConstCopowers ((SSet.sk n).obj K) C]
variable [((truncation n).obj V).HasCoskeleton]

/-- Objectwise coskeleton identifies the constant-object mapping presheaf indexed by `K` with
the one indexed by `sk n K`. -/
@[stacks 018V "coskeleton constant-restriction comparison"]
noncomputable def constRestrictionIso :
    constRestriction K ((truncation n).obj V).coskeleton ≅
      constRestriction ((SSet.sk n).obj K) V :=
  rightKan.constRestrictionIso n K V
    ((SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit
      ((truncation n).obj V))

end ConstantRestriction

namespace degree

section Representation

variable (n q : ℕ) (V : SimplicialObject C)
variable [HasConstCopowers (Δ[q] : SSet.{w}) C]
variable [HasConstCopowers ((SSet.sk n).obj (Δ[q] : SSet.{w})) C]
variable [((truncation n).obj V).HasCoskeleton]

/-- The Hom equivalence identifying degree `q` of an objectwise `n`-coskeleton with the
constant-object mapping presheaf indexed by `sk n Δ[q]`. -/
@[stacks 018V "coskeleton degree as a skeleton-indexed mapping presheaf"]
noncomputable def homEquiv (X : C) :
    (X ⟶ ((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q))) ≃
      (constRestriction ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).obj (op X) :=
  (copower.stdSimplex.homEquiv.{w} q X ((truncation n).obj V).coskeleton).symm.trans
    (copower.coskeleton.homEquiv n (Δ[q] : SSet.{w}) V X)

/-- The coskeleton-degree representing equivalence is natural in the constant object. -/
@[stacks 018V "coskeleton degree representation naturality"]
theorem homEquiv.comp {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ ((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q))) :
    homEquiv n q V X (f ≫ g) =
      (constRestriction ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).map f.op
        (homEquiv n q V Y g) := sorry

/-- Degree `q` of an objectwise `n`-coskeleton represents the constant-object mapping presheaf
indexed by `sk n Δ[q]`. -/
@[stacks 018V "coskeleton degree represents the constant restriction"]
noncomputable def representableBy :
    (constRestriction ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).RepresentableBy
      (((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q))) where
  homEquiv {X} := homEquiv n q V X
  homEquiv_comp := homEquiv.comp n q V

end Representation

namespace zero

section Comparison

variable (n q : ℕ) (V : SimplicialObject C)
variable [HasConstCopowers (Δ[q] : SSet.{w}) C]
variable [HasCopowers ((SSet.sk n).obj (Δ[q] : SSet.{w})) C]
variable [((truncation n).obj V).HasCoskeleton]

/-- Compare a coskeleton degree with degree zero of any explicit representation of the
corresponding global internal-hom presheaf. -/
@[stacks 018V "explicit coskeleton-degree zero-term comparison"]
noncomputable def ofRepresentableBy.iso {M : SimplicialObject C}
    (R : (presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).RepresentableBy M) :
    ((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q)) ≅
      M.obj (op (SimplexCategory.mk 0)) :=
  Functor.RepresentableBy.uniqueUpToIso
    (degree.representableBy n q V)
    (internalHom.zero.representableBy
      ((SSet.sk n).obj (Δ[q] : SSet.{w})) V R)

/-- The forward coskeleton-degree comparison identifies the universal elements of its two
explicit representations. -/
@[simp, stacks 018V "coskeleton-degree comparison on universal elements"]
theorem ofRepresentableBy.iso.hom_apply {M : SimplicialObject C}
    (R : (presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).RepresentableBy M) :
    (internalHom.zero.representableBy
      ((SSet.sk n).obj (Δ[q] : SSet.{w})) V R).homEquiv
        (ofRepresentableBy.iso n q V R).hom =
      (degree.representableBy n q V).homEquiv (𝟙 _) := sorry

/-- The inverse coskeleton-degree comparison identifies the universal elements of its two
explicit representations. -/
@[simp, stacks 018V "coskeleton-degree comparison on universal elements"]
theorem ofRepresentableBy.iso.inv_apply {M : SimplicialObject C}
    (R : (presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).RepresentableBy M) :
    (degree.representableBy n q V).homEquiv
        (ofRepresentableBy.iso n q V R).inv =
      (internalHom.zero.representableBy
        ((SSet.sk n).obj (Δ[q] : SSet.{w})) V R).homEquiv (𝟙 _) := sorry

/-- Degree `q` of an objectwise `n`-coskeleton is canonically isomorphic to degree zero of the
chosen internal mapping object from `sk n Δ[q]`. -/
@[stacks 018V "coskeleton degree and internal-hom zero term"]
noncomputable def iso
    [Functor.IsRepresentable
      (presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V)] :
    ((truncation n).obj V).coskeleton.obj (op (SimplexCategory.mk q)) ≅
      (internalHom ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).obj
        (op (SimplexCategory.mk 0)) :=
  ofRepresentableBy.iso n q V
    (presheaf ((SSet.sk n).obj (Δ[q] : SSet.{w})) V).representableBy

end Comparison

end zero

end degree

end CategoryTheory.SimplicialObject.internalHom.coskeleton

namespace CategoryTheory.SimplicialObject.internalHom.deltaOne

variable {C : Type u} [Category.{v} C]
variable (T : SimplicialObject C)
variable [HasCopowers (Δ[0] : SSet.{w}) C]
variable [HasCopowers (Δ[1] : SSet.{w}) C]
variable [HasInternalHom (Δ[0] : SSet.{w}) T]
variable [HasInternalHom (Δ[1] : SSet.{w}) T]
variable [HasBinaryProduct (internalHom (Δ[0] : SSet.{w}) T)
  (internalHom (Δ[0] : SSet.{w}) T)]

/-- The endpoint-pair morphism from the internal mapping object out of the simplicial interval
to the product of the two internal mapping objects out of a point. -/
@[stacks 01GQ "endpoint pair on the simplicial internal hom"]
def endpointPair :
    internalHom (Δ[1] : SSet.{w}) T ⟶
      internalHom (Δ[0] : SSet.{w}) T ⨯ internalHom (Δ[0] : SSet.{w}) T :=
  prod.lift
    (precomp (SSet.stdSimplex.δ (1 : Fin 2)) T)
    (precomp (SSet.stdSimplex.δ (0 : Fin 2)) T)

namespace endpointPair

/-- The first projection of the endpoint-pair morphism is restriction to the zero endpoint. -/
@[simp, reassoc]
theorem fst :
    endpointPair T ≫ prod.fst =
      precomp (SSet.stdSimplex.δ (1 : Fin 2)) T := sorry

/-- The second projection of the endpoint-pair morphism is restriction to the one endpoint. -/
@[simp, reassoc]
theorem snd :
    endpointPair T ≫ prod.snd =
      precomp (SSet.stdSimplex.δ (0 : Fin 2)) T := sorry

/-- Equation 25.9.1.1 (Tag 01GQ), in degree-independent form: the endpoint-pair map commutes
with the unit from a simplicial object to the coskeleton of its truncation. -/
@[stacks 01GQ "endpoint pair and the coskeleton unit"]
theorem coskUnitSq (n q : ℕ) [Truncated.HasCoskeletons C n] :
    CommSq
      ((endpointPair T).app (op ⦋q⦌))
      (((coskAdj n).unit.app (internalHom (Δ[1] : SSet.{w}) T)).app (op ⦋q⦌))
      (((coskAdj n).unit.app
        (internalHom (Δ[0] : SSet.{w}) T ⨯ internalHom (Δ[0] : SSet.{w}) T)).app
          (op ⦋q⦌))
      (((cosk n).map (endpointPair T)).app (op ⦋q⦌)) := sorry

end endpointPair

end CategoryTheory.SimplicialObject.internalHom.deltaOne
