module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import stacks_project.Chap96.Definition_96_26_1_QC

/-!
# Top cohomology of a bounded-above quasi-coherent derived object

In the situation of Definition 96.26.1, the last nonvanishing cohomology sheaf of
an object of `QC(𝒳)` is a quasi-coherent module on `(𝒳_affine, 𝒪)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ModulesOnCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The canonical standard derived-category structure on modules over the
chaotic ringed site `(𝒳_affine, 𝒪)`. -/
instance affineStructureSheaf_moduleCat_hasDerivedCategory :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1}
    (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))

namespace QC

/-- The cohomology sheaf `H^i(M)` of a quasi-coherent derived object on `𝒳`. -/
abbrev cohomology (M : QC X) (i : ℤ) :
    SheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology (affineSite X))
        (affineStructureSheaf X)) :=
  (DerivedCategory.homologyFunctor
      (SheafOfModules.{u + 1}
        (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology (affineSite X))
          (affineStructureSheaf X)))
      i).obj M.obj

/-- `QC.cohomology M i` is the degree-`i` homology sheaf of the underlying derived
module of `M`. -/
theorem cohomology_eq (M : QC X) (i : ℤ) :
    cohomology M i =
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{u + 1}
            (ringSheaf.{u + 1, u, u + 1} (⊥ : GrothendieckTopology (affineSite X))
              (affineStructureSheaf X)))
          i).obj M.obj :=
  sorry

end QC

/-- Lemma 96.26.2: in the situation of Definition 96.26.1, if `M` is an object of
`QC(𝒳)` and `b ∈ ℤ` satisfies `H^i(M) = 0` for all `i > b`, then `H^b(M)` is a
quasi-coherent module on `(𝒳_affine, 𝒪)` in the sense of Lemma 96.25.1. -/
@[stacks 0H0I]
theorem cohomology_isQuasicoherent (M : QC X) (b : ℤ)
    (hvanish : ∀ i : ℤ, b < i → IsZero (QC.cohomology M i)) :
    (QC.cohomology M b).IsQuasicoherent :=
  sorry

/-- If a quasi-coherent derived object is bounded above by `b` in the canonical
t-structure, then its degree-`b` cohomology sheaf is quasi-coherent. -/
theorem cohomology_isQuasicoherent_of_isLE (M : QC X) (b : ℤ)
    (hM : M.obj.IsLE b) :
    (QC.cohomology M b).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
