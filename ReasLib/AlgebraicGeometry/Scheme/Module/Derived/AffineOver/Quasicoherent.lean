/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic

/-!
# Quasi-coherent derived modules on all affine schemes over a scheme

This module specializes the comparison-defined quasi-coherence condition for a chaotic
ringed site to the category of all affine schemes over a fixed scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The global-functions sheaf on the chaotic category of all affine schemes over `S`. -/
def affineOverChaoticStructureSheaf (S : Scheme.{u}) :
    Sheaf (⊥ : GrothendieckTopology S.AffineOver) CommRingCat.{u + 1} :=
  ⟨Scheme.Over.commStructurePresheaf (Scheme.AffineOver.forget S),
    Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of the chaotic structure sheaf on affine schemes over `S`. -/
theorem affineOverChaoticStructureSheaf_obj (S : Scheme.{u}) :
    (affineOverChaoticStructureSheaf S).obj =
      Scheme.Over.commStructurePresheaf (Scheme.AffineOver.forget S) := sorry

/-- The canonical comparison quasi-coherence property on the chaotic category of all affine
schemes over `S`. -/
abbrev affineOverQCProperty (S : Scheme.{u}) : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology S.AffineOver)
        (affineOverChaoticStructureSheaf S))) :=
  CategoryTheory.ModulesOnCategory.Chaotic.isQuasiCoherent.{u + 1, u, u}
    (affineOverChaoticStructureSheaf S)

/-- The comparison-defined category of quasi-coherent derived modules on all affine schemes
over `S`. -/
abbrev AffineOverQC (S : Scheme.{u}) :=
  (affineOverQCProperty S).FullSubcategory

end AlgebraicGeometry.Scheme.DerivedQCoh
