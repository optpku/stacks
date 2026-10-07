module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

@[expose] public section
open CategoryTheory Opposite
open AlgebraicGeometry
universe u
namespace CrystallineAffineSheafExtension

variable {A : Type u} [CommRing A] (Y : Scheme.{u})

/-- The topological sheaf spelling carries the canonical pointwise
preadditive structure of the same category of site sheaves. -/
noncomputable instance baseSheafPreadditive : Preadditive (TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat) :=
  inferInstanceAs (Preadditive (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u} A)))

/-- The actual inclusion of affine opens into all opens of Y. -/
abbrev affineInclusion := inducedFunctor (fun U : Y.affineOpens ↦ U.1)

/-- The inclusion of affine opens has precisely the affine basis as range. -/
theorem affineBasis : TopologicalSpace.Opens.IsBasis
    (Set.range (fun U : Y.affineOpens ↦ U.1)) := by
  have h : Set.range (fun U : Y.affineOpens ↦ U.1) = Y.affineOpens := by
    ext U
    simp
  rw [h]
  exact Y.isBasis_affineOpens

/-- Extend a specified natural transformation on affine opens between
genuine A-module sheaves. The sheaf condition determines the extension;
no global-section tensor identification is used. -/
noncomputable def extend (K L : TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat)
    (d : (affineInclusion Y).op ⋙ K.obj ⟶ (affineInclusion Y).op ⋙ L.obj) : K ⟶ L :=
  ⟨TopCat.Sheaf.restrictHomEquivHom K.obj L (affineBasis Y) d⟩

/-- The extension recovers exactly its specified affine components. -/
theorem extend_affine (K L : TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat)
    (d : (affineInclusion Y).op ⋙ K.obj ⟶ (affineInclusion Y).op ⋙ L.obj)
    (U : Y.affineOpens) :
    (extend Y K L d).hom.app (op U.1) = d.app (op U) :=
  TopCat.Sheaf.extend_hom_app K.obj L (affineBasis Y) d U

/-- Two A-linear sheaf maps coincide when their actual affine components
coincide. This is the uniqueness gate for a sheaf-level connection. -/
theorem hom_ext {K L : TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat}
    (f g : K ⟶ L) (h : ∀ U : Y.affineOpens, f.hom.app (op U.1) = g.hom.app (op U.1)) :
    f = g := by
  have he : f.hom = g.hom := TopCat.Sheaf.hom_ext K.obj L (affineBasis Y) h
  cases f
  cases g
  cases he
  rfl

end CrystallineAffineSheafExtension
