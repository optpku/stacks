/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

/-!
# Property classes of algebraic-space morphisms as étale-local lifts

Stacks defines flat, syntomic, unramified, perfect, local complete intersection,
locally of finite type, locally quasi-finite and locally of finite presentation
morphisms of algebraic spaces by one pattern: the scheme property holds on the
top arrow of every commutative square with étale vertical arrows from schemes.
The single owner of that pattern is `AlgebraicSpace.etaleLocal`; each property
class is identified with its lift here.

The lift can equivalently be tested on the bundled squares `EtaleSquare f`
whose charts are objects of the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The étale-local lift of `P` holds exactly when `P` holds for the scheme
morphism of every bundled étale square over `f`. -/
theorem etaleLocal_iff_forall_etaleSquare (P : MorphismProperty Scheme.{u}) (f : X ⟶ Y) :
    etaleLocal P f ↔ ∀ square : EtaleSquare f, P square.map.left :=
  sorry

/-- Flatness of a morphism of algebraic spaces is the étale-local lift of
flatness of scheme morphisms. -/
theorem flat_iff_etaleLocal (f : X ⟶ Y) :
    Flat f ↔ etaleLocal @AlgebraicGeometry.Flat f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Syntomicity of a morphism of algebraic spaces is the étale-local lift of
syntomicity of scheme morphisms. -/
theorem syntomic_iff_etaleLocal (f : X ⟶ Y) :
    Syntomic f ↔ etaleLocal @AlgebraicGeometry.Syntomic f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Unramifiedness of a morphism of algebraic spaces is the étale-local lift of
unramifiedness of scheme morphisms. -/
theorem unramified_iff_etaleLocal (f : X ⟶ Y) :
    Unramified f ↔ etaleLocal @AlgebraicGeometry.Unramified f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- A morphism of algebraic spaces is a local complete intersection exactly
when it has the étale-local lift of the scheme local-complete-intersection
property. -/
theorem isLocalCompleteIntersection_iff_etaleLocal (f : X ⟶ Y) :
    IsLocalCompleteIntersection f ↔
      etaleLocal (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection) f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Perfectness of a morphism of algebraic spaces is the étale-local lift of
perfectness of scheme morphisms. -/
theorem perfect_iff_etaleLocal (f : X ⟶ Y) :
    Perfect f ↔ etaleLocal (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Local finite type of a morphism of algebraic spaces is the étale-local lift
of local finite type of scheme morphisms. -/
theorem locallyOfFiniteType_iff_etaleLocal (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ etaleLocal @AlgebraicGeometry.LocallyOfFiniteType f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Local quasi-finiteness of a morphism of algebraic spaces is the étale-local
lift of local quasi-finiteness of scheme morphisms. -/
theorem locallyQuasiFinite_iff_etaleLocal (f : X ⟶ Y) :
    LocallyQuasiFinite f ↔ etaleLocal @AlgebraicGeometry.LocallyQuasiFinite f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

/-- Local finite presentation of a morphism of algebraic spaces is the
étale-local lift of local finite presentation of scheme morphisms. -/
theorem locallyOfFinitePresentation_iff_etaleLocal (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      etaleLocal @AlgebraicGeometry.LocallyOfFinitePresentation f :=
  ⟨fun h => (etaleLocal_iff f).2 fun a b g ha hb w => h.of_etale a b g ha hb w,
    fun h => ⟨fun a b g ha hb w => (etaleLocal_iff f).1 h a b g ha hb w⟩⟩

end AlgebraicGeometry.AlgebraicSpace
