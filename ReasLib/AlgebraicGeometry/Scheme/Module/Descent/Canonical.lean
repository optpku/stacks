module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Canonical descent data for quasi-coherent modules

Quasi-coherent modules on a scheme restrict to canonical descent data along any indexed family
of scheme morphisms. Effectivity is membership in the essential image of this restriction
functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.QCoh

variable {I : Type v} {S : Scheme.{u}} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)

/-- Pullback along an indexed family of scheme morphisms carries quasi-coherent modules to
descent data whose components are quasi-coherent. -/
theorem canonicalFunctor_mapsTo :
    Scheme.quasiCoherentModuleProperty S ≤
      (descentProperty X f).inverseImage
        (Modules.descentPseudofunctor.toDescentData f) := sorry

/-- The functor sending a quasi-coherent module to its canonical descent datum along an indexed
family of scheme morphisms. -/
noncomputable def canonicalFunctor : QCoh S ⥤ DescentData X f :=
  ObjectProperty.FullSubcategory.restrict
    (Modules.descentPseudofunctor.toDescentData f) (canonicalFunctor_mapsTo X f)

namespace canonicalFunctor

/-- A morphism between canonical descent data is componentwise pullback of the original
morphism. -/
theorem map_hom {F G : QCoh S} (g : F ⟶ G) (i : I) :
    ((canonicalFunctor X f).map g).hom.hom i =
      (Modules.descentPseudofunctor.map (f i).op.toLoc).toFunctor.map g.hom := sorry

end canonicalFunctor

namespace DescentData

/-- The canonical quasi-coherent descent datum of a quasi-coherent module along an indexed
family of scheme morphisms. -/
noncomputable def canonical (F : QCoh S) : DescentData X f :=
  (canonicalFunctor X f).obj F

/-- Forgetting quasi-coherence from a canonical datum recovers the canonical module descent
datum. -/
theorem canonical_obj (F : QCoh S) :
    (canonical X f F).obj =
      (Modules.descentPseudofunctor.toDescentData f).obj F.obj := sorry

/-- The component of a canonical descent datum at an index is pullback along the corresponding
scheme morphism. -/
theorem canonical_obj_obj (F : QCoh S) (i : I) :
    (canonical X f F).obj.obj i = (Modules.pullback (f i)).obj F.obj := sorry

/-- The trivial descent datum of a quasi-coherent module is its canonical descent datum for the
singleton family consisting of the identity morphism. -/
noncomputable def trivial (F : QCoh S) :
    DescentData (fun _ : Unit ↦ S) (fun _ ↦ 𝟙 S) :=
  canonical (fun _ : Unit ↦ S) (fun _ ↦ 𝟙 S) F

/-- The unique component of the trivial descent datum is pullback along the identity morphism. -/
theorem trivial_obj_obj (F : QCoh S) :
    (trivial F).obj.obj () = (Modules.pullback (𝟙 S)).obj F.obj := sorry

end DescentData

end AlgebraicGeometry.Scheme.QCoh

namespace AlgebraicGeometry.Scheme.QCoh.DescentData

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- A quasi-coherent descent datum is effective when it lies in the essential image of the
canonical descent functor. -/
abbrev IsEffective (D : DescentData X f) : Prop :=
  (QCoh.canonicalFunctor X f).essImage D

/-- A quasi-coherent descent datum is effective exactly when it is isomorphic to the canonical
datum of a quasi-coherent module on the base scheme. -/
theorem isEffective_iff (D : DescentData X f) :
    D.IsEffective ↔ ∃ F : QCoh S, Nonempty (canonical X f F ≅ D) := sorry

namespace IsEffective

/-- Every canonical quasi-coherent descent datum is effective. -/
theorem of_canonical (F : QCoh S) : IsEffective (canonical X f F) := sorry

/-- Effectivity is preserved by isomorphisms of quasi-coherent descent data. -/
theorem ofIso {D E : DescentData X f} (e : D ≅ E) (hD : IsEffective D) :
    IsEffective E := sorry

end IsEffective

end AlgebraicGeometry.Scheme.QCoh.DescentData
