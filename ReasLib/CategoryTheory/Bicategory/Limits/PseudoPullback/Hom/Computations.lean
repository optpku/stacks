module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Construction

/-!
# Computations for morphisms of readable pseudopullback cones

This leaf contains the reduction, reconstruction, compatibility, and extensionality API for the
readable cone constructors and projections. Consumers that only need the underlying apex and leg
cells can import `Hom.Basic`; consumers constructing cells import `Hom.Construction`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The forward cell of the first-leg comparison is its underlying noninvertible comparison
cell. -/
@[simp]
theorem fstIso.hom [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (fstIso u).hom = fstFac u := sorry

/-- The inverse cell of the first-leg comparison is the inverse of its underlying cell. -/
@[simp]
theorem fstIso.inv [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (fstIso u).inv = (asIso (fstFac u)).inv := sorry

/-- The forward cell of the second-leg comparison is its underlying noninvertible comparison
cell. -/
@[simp]
theorem sndIso.hom [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (sndIso u).hom = sndFac u := sorry

/-- The inverse cell of the second-leg comparison is the inverse of its underlying cell. -/
@[simp]
theorem sndIso.inv [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (sndIso u).inv = (asIso (sndFac u)).inv := sorry

/-- The forward cell of the central comparison is its underlying noninvertible comparison cell. -/
@[simp]
theorem baseIso.hom [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (baseIso u).hom = baseFac u := sorry

/-- The inverse cell of the central comparison is the inverse of its underlying cell. -/
@[simp]
theorem baseIso.inv [IsLocallyGroupoid B]
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    (baseIso u).inv = (asIso (baseFac u)).inv := sorry

/-- The apex map of a constructed readable pseudopullback-cone morphism is the supplied map. -/
@[simp]
theorem homMk_map {S T : PseudoPullbackCone f g} (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ⟶ S.toPseudoCone.π) :
    map (homMk l e) = l := sorry

/-- The comparison modification of a constructed readable pseudopullback-cone morphism is the
supplied modification. -/
@[simp]
theorem homMk_fac {S T : PseudoPullbackCone f g} (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ⟶ S.toPseudoCone.π) :
    fac (homMk l e) = e := sorry

/-- Readable pseudopullback-cone morphisms are determined by their apex maps and normalized
comparison modifications. -/
@[ext (iff := false)]
theorem hom_ext {S T : PseudoPullbackCone f g} (u v : S ⟶ T)
    (hmap : map u = map v)
    (hfac : (T.toPseudoCone.comparison S.pt).map (eqToHom hmap) ≫ fac v = fac u) :
    u = v := sorry

/-- Reconstructing a readable pseudopullback-cone morphism from its apex map and comparison
modification recovers the original morphism. -/
@[simp]
theorem homMk_map_fac {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    homMk (map u) (fac u) = u := sorry

/-- Every readable pseudopullback-cone `2`-morphism is compatible with the normalized
comparison modifications of its source and target. -/
theorem map₂_fac {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    (T.toPseudoCone.comparison S.pt).map (map₂ η) ≫ fac v = fac u := sorry

/-- The apex cell of a constructed readable pseudopullback-cone `2`-morphism is the supplied
cell. -/
@[simp]
theorem hom₂Mk_map₂ {S T : PseudoPullbackCone f g} {u v : S ⟶ T}
    (η : map u ⟶ map v)
    (comm : (T.toPseudoCone.comparison S.pt).map η ≫ fac v = fac u) :
    map₂ (hom₂Mk η comm) = η := sorry

/-- Readable pseudopullback-cone `2`-morphisms are determined by their cells between apex maps. -/
@[ext]
theorem hom₂_ext {S T : PseudoPullbackCone f g} {u v : S ⟶ T} {η θ : u ⟶ v}
    (h : map₂ η = map₂ θ) : η = θ := sorry

/-- Reconstructing a readable pseudopullback-cone `2`-morphism from its apex cell and
compatibility equation recovers the original `2`-morphism. -/
@[simp]
theorem hom₂Mk_map₂_fac {S T : PseudoPullbackCone f g} {u v : S ⟶ T} (η : u ⟶ v) :
    hom₂Mk (map₂ η) (map₂_fac η) = η := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
