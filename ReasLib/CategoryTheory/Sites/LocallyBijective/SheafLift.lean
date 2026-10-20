/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Maps into sheaves along a locally bijective presheaf map

The actual inverse to precomposition glues the supplied sheaf's images of
local preimages. No assumption about the existence of sheafification, or an
inequality between the site and value universes, is required.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Presheaf.LocallyBijective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)

/-- A local preimage is mapped by the original supplied map into the target sheaf. -/
def liftFamily (Z : Cᵒᵖ ⥤ Type w) (f : F ⟶ Z) {U : C} (s : G.obj (op U)) :
    Presieve.FamilyOfElements Z (Presheaf.imageSieve η s).arrows :=
  fun _ g hg ↦ f.app _ (Presheaf.localPreimage η s g hg)

/-- Local injectivity makes the local images compatible after using the
separatedness of the original supplied sheaf. -/
theorem liftFamily_compatible (hI : Presheaf.IsLocallyInjective J η)
    (Z : Cᵒᵖ ⥤ Type w) (hZ : Presheaf.IsSheaf J Z) (f : F ⟶ Z)
    {U : C} (s : G.obj (op U)) : (liftFamily η Z f s).Compatible := sorry

/-- The actual glued section uses only the original sheaf's own amalgamation witness. -/
def liftSection (hI : Presheaf.IsLocallyInjective J η)
    (hS : Presheaf.IsLocallySurjective J η)
    (Z : Cᵒᵖ ⥤ Type w) (hZ : Presheaf.IsSheaf J Z) (f : F ⟶ Z)
    {U : C} (s : G.obj (op U)) : Z.obj (op U) := by
  letI := hS
  let H := ((isSheaf_iff_isSheaf_of_type J Z).1 hZ) _ (Presheaf.imageSieve_mem J η s)
  exact H.amalgamate (liftFamily η Z f s) (liftFamily_compatible J η hI Z hZ f s)

/-- The actual inverse map to precomposition with the supplied locally bijective map. -/
def lift (hI : Presheaf.IsLocallyInjective J η)
    (hS : Presheaf.IsLocallySurjective J η)
    (Z : Cᵒᵖ ⥤ Type w) (hZ : Presheaf.IsSheaf J Z) (f : F ⟶ Z) : G ⟶ Z where
  app _ := ↾fun s ↦ liftSection J η hI hS Z hZ f s
  naturality := by sorry

/-- The specified glued map extends the original supplied map. -/
theorem lift_fac (hI : Presheaf.IsLocallyInjective J η)
    (hS : Presheaf.IsLocallySurjective J η)
    (Z : Cᵒᵖ ⥤ Type w) (hZ : Presheaf.IsSheaf J Z) (f : F ⟶ Z) :
    η ≫ lift J η hI hS Z hZ f = f := sorry

/-- Equality after precomposition is detected on the actual local-preimage covers. -/
theorem precomp_injective (hS : Presheaf.IsLocallySurjective J η)
    (Z : Cᵒᵖ ⥤ Type w) (hZ : Presheaf.IsSheaf J Z)
    (f g : G ⟶ Z) (h : η ≫ f = η ≫ g) : f = g := sorry

/-- A locally bijective Type-valued presheaf map is local, with the explicitly
glued inverse on each Hom set of maps to a sheaf. -/
theorem mem_W (hI : Presheaf.IsLocallyInjective J η)
    (hS : Presheaf.IsLocallySurjective J η) : J.W η := by
  intro Z hZ
  exact ⟨fun f g h ↦ precomp_injective J η hS Z hZ f g h,
    fun f ↦ ⟨lift J η hI hS Z hZ f, lift_fac J η hI hS Z hZ f⟩⟩

end CategoryTheory.Presheaf.LocallyBijective
