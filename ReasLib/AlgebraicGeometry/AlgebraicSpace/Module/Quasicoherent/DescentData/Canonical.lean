module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Pullback

/-!
# Canonical descent data for quasi-coherent modules on algebraic spaces

Quasi-coherent modules on an algebraic space restrict to canonical descent data along any
indexed family of morphisms of algebraic spaces. Effectivity is membership in the essential
image of this restriction functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {I : Type v} {S : Scheme.{u}} {X : AlgebraicSpace S}

section
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- Pullback along an indexed family of morphisms of algebraic spaces carries quasi-coherent
modules to descent data whose components are quasi-coherent. -/
theorem canonicalFunctor_mapsTo :
    quasiCoherentModuleProperty X ≤
      (descentProperty Xᵢ f).inverseImage
        ((Modules.descentPseudofunctor S).toDescentData f) := sorry

/-- The functor sending a quasi-coherent module to its canonical descent datum along an indexed
family of morphisms of algebraic spaces. -/
noncomputable def canonicalFunctor : QCoh X ⥤ DescentData Xᵢ f :=
  ObjectProperty.FullSubcategory.restrict
    ((Modules.descentPseudofunctor S).toDescentData f) (canonicalFunctor_mapsTo Xᵢ f)

namespace canonicalFunctor

/-- A morphism between canonical descent data is componentwise pullback of the original
morphism. -/
theorem map_hom {F G : QCoh X} (g : F ⟶ G) (i : I) :
    ((canonicalFunctor Xᵢ f).map g).hom.hom i =
      ((Modules.descentPseudofunctor S).map (f i).op.toLoc).toFunctor.map g.hom := sorry

end canonicalFunctor

namespace DescentData

/-- The canonical quasi-coherent descent datum of a quasi-coherent module along an indexed
family of morphisms of algebraic spaces. -/
noncomputable def canonical (F : QCoh X) : DescentData Xᵢ f :=
  (canonicalFunctor Xᵢ f).obj F

/-- Forgetting quasi-coherence from a canonical datum recovers the canonical module descent
datum. -/
theorem canonical_obj (F : QCoh X) :
    (canonical Xᵢ f F).obj =
      ((Modules.descentPseudofunctor S).toDescentData f).obj F.obj := sorry

/-- The component of a canonical descent datum at an index is pullback along the corresponding
morphism of algebraic spaces. -/
theorem canonical_obj_obj (F : QCoh X) (i : I) :
    (canonical Xᵢ f F).obj.obj i = (Modules.pullback (f i)).obj F.obj := sorry

/-- The trivial descent datum of a quasi-coherent module is its canonical descent datum for the
singleton family consisting of the identity morphism. -/
noncomputable def trivial (F : QCoh X) :
    DescentData (fun _ : Unit ↦ X) (fun _ ↦ 𝟙 X) :=
  canonical (fun _ : Unit ↦ X) (fun _ ↦ 𝟙 X) F

/-- The unique component of the trivial descent datum is pullback along the identity morphism. -/
theorem trivial_obj_obj (F : QCoh X) :
    (trivial F).obj.obj () = (Modules.pullback (𝟙 X)).obj F.obj := sorry

/-- The canonical descent datum of `F` is isomorphic to the pullback of the trivial descent
datum along the identity-family morphism `{Xᵢ → X} → {X → X}`. -/
theorem canonical_iso_pullback_trivial (F : QCoh X) :
    Nonempty
      (canonical Xᵢ f F ≅
        (Pullback.functorOfHom (fun _ : I ↦ ()) f
            (fun i ↦ (rfl : f i ≫ 𝟙 X = f i ≫ 𝟙 X))).obj (trivial F)) := sorry

end DescentData

end

namespace DescentData

variable {Xᵢ : I → AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X}

/-- A quasi-coherent descent datum is effective when it lies in the essential image of the
canonical descent functor. -/
abbrev IsEffective (D : DescentData Xᵢ f) : Prop :=
  (canonicalFunctor Xᵢ f).essImage D

/-- A quasi-coherent descent datum is effective exactly when it is isomorphic to the canonical
datum of a quasi-coherent module on the target algebraic space. -/
theorem isEffective_iff (D : DescentData Xᵢ f) :
    D.IsEffective ↔ ∃ F : QCoh X, Nonempty (canonical Xᵢ f F ≅ D) := sorry

namespace IsEffective

/-- Every canonical quasi-coherent descent datum is effective. -/
theorem of_canonical (F : QCoh X) : IsEffective (canonical Xᵢ f F) := sorry

/-- Effectivity is preserved by isomorphisms of quasi-coherent descent data. -/
theorem ofIso {D E : DescentData Xᵢ f} (e : D ≅ E) (hD : IsEffective D) :
    IsEffective E := sorry

end IsEffective

end DescentData

end AlgebraicGeometry.AlgebraicSpace.QCoh
