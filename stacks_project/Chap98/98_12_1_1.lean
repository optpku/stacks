module

public import stacks_project.Chap98.«98_12_1_1_Hat»
import Mathlib.Tactic.CrossRefAttribute

/-!
# The morphism `hat x` of predeformation categories

Stacks tag 07XE: 2-Yoneda sends an object `x` over `U` to a 1-morphism
`(Sch/U)_fppf ⟶ 𝒳`, which induces a morphism of predeformation categories
`hat x : ℱ_{(Sch/U)_fppf, κ(u0), u0} ⟶ ℱ_{𝒳, κ(u0), x0}` over `C_Λ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids (toFunctor fiberFunctor slice)
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (U : Over S) (u0 : U.left)
variable [Algebra Λ (residueType U u0)]
variable [Module.Finite Λ (residueType U u0)]
variable (kToS : Spec (CommRingCat.of (residueType U u0)) ⟶ S)
variable [LocallyOfFiniteType kToS]
variable (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (residueType U u0))) ≫ openImmersion =
      kToS)
variable (h_kToS : kToS = residuePointToS U u0)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x : X.p.Fiber U)

/-- 98.12.1.1: given a locally Noetherian scheme `S`, a morphism `U ⟶ S` locally of
finite type, a finite type point `u0` of `U` with residue field `k = κ(u0)`, a
category `𝒳` fibred in groupoids over `(Sch/S)_fppf`, and an object `x` of `𝒳`
over `U`, 2-Yoneda sends `x` to a 1-morphism `(Sch/U)_fppf ⟶ 𝒳` and thereby
induces a morphism of predeformation categories
`hat x : ℱ_{(Sch/U)_fppf, k, u0} ⟶ ℱ_{𝒳, k, x0}` over `C_Λ`. -/
@[stacks 07XE]
def hat [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    predeformation openImmersion h_factor (slice U)
      (residueFiber U u0 kToS h_kToS) ⥤ᵇ
      predeformation openImmersion h_factor X
        (residueObject U u0 kToS h_kToS X x) :=
  hatFunctor openImmersion U u0 kToS h_factor h_kToS X x

/-- Applying `hat` preserves the Artinian base and sends the target and residue
morphism along the 2-Yoneda representative of `x`. -/
theorem hat_obj [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    (ξ : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)) :
    ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).base = ξ.base ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).target =
        (fiberFunctor (representative x) (specOver openImmersion ξ.base)).obj ξ.target ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).fromResidue =
        (toFunctor (representative x)).map ξ.fromResidue :=
  sorry

/-- Applying `hat` preserves the Artinian base homomorphism and sends the reversed
total-category arrow along the 2-Yoneda representative of `x`. -/
theorem hat_map [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    {ξ η : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)}
    (f : Hom ξ η) :
    ((hat openImmersion U u0 kToS h_factor h_kToS X x).map f).baseHom = f.baseHom ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).map f).hom =
        (toFunctor (representative x)).map f.hom :=
  sorry

/-- `hat` is a morphism of categories over `ArtinianLocalAlgCat Λ κ(u0)`. -/
theorem hat_w [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    (hat openImmersion U u0 kToS h_factor h_kToS X x).toFunctor ⋙
        forget openImmersion kToS h_factor X (residueObject U u0 kToS h_kToS X x) =
      forget openImmersion kToS h_factor (slice U)
        (residueFiber U u0 kToS h_kToS) :=
  sorry

/-- `hat` is the predeformation functoriality of the 2-Yoneda representative of `x`
at the canonical residue-field point of the finite type point `u0`. -/
theorem hat_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    hat openImmersion U u0 kToS h_factor h_kToS X x =
      map openImmersion h_factor (representative x)
        (residueFiber U u0 kToS h_kToS) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
