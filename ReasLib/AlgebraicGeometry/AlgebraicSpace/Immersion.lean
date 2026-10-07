module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Immersions of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is an immersion, closed immersion, or
open immersion when its transformation of functors of points is representable and all
represented pullbacks have the corresponding scheme morphism property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- A morphism of algebraic spaces over `S` is an immersion if its transformation of functors
of points is representable and every represented pullback is an immersion of schemes. -/
class IsImmersion {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) : Prop where
  /-- The underlying transformation of functors of points has the relative immersion
  property. -/
  presheaf : (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})).presheaf f

/-- A morphism of algebraic spaces over `S` is a closed immersion if its transformation of
functors of points is representable and every represented pullback is a closed immersion
of schemes. -/
class IsClosedImmersion {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) : Prop where
  /-- The underlying transformation of functors of points has the relative closed-immersion
  property. -/
  presheaf :
    (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf f

/-- A morphism of algebraic spaces over `S` is an open immersion if its transformation of
functors of points is representable and every represented pullback is an open immersion
of schemes. -/
class IsOpenImmersion {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) : Prop where
  /-- The underlying transformation of functors of points has the relative open-immersion
  property. -/
  presheaf : (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf f

/-- A morphism of algebraic spaces is an immersion iff the corresponding transformation of
functors of points has the relative immersion property. -/
theorem isImmersion_iff {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsImmersion f ↔
      (over (@AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A morphism of algebraic spaces is an immersion iff it is representable and every
represented pullback over a scheme is an immersion of schemes. -/
theorem IsImmersion.spec {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsImmersion snd.left := sorry

/-- The identity morphism of an algebraic space is an immersion. -/
instance IsImmersion.id {S : Scheme.{u}} {F : AlgebraicSpace S} : IsImmersion (𝟙 F) := sorry

/-- A morphism of algebraic spaces is a closed immersion iff the corresponding transformation of
functors of points has the relative closed-immersion property. -/
theorem isClosedImmersion_iff {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsClosedImmersion f ↔
      (over (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A morphism of algebraic spaces is a closed immersion iff it is representable and every
represented pullback over a scheme is a closed immersion of schemes. -/
theorem IsClosedImmersion.spec {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsClosedImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsClosedImmersion snd.left := sorry

/-- The identity morphism of an algebraic space is a closed immersion. -/
instance IsClosedImmersion.id {S : Scheme.{u}} {F : AlgebraicSpace S} :
    IsClosedImmersion (𝟙 F) := sorry

/-- A morphism of algebraic spaces is an open immersion iff the corresponding transformation of
functors of points has the relative open-immersion property. -/
theorem isOpenImmersion_iff {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsOpenImmersion f ↔
      (over (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf f := sorry

/-- A morphism of algebraic spaces is an open immersion iff it is representable and every
represented pullback over a scheme is an open immersion of schemes. -/
theorem IsOpenImmersion.spec {S : Scheme.{u}} {F G : AlgebraicSpace S} (f : F ⟶ G) :
    IsOpenImmersion f ↔
      yoneda.relativelyRepresentable f ∧
        ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G.functorOfPoints)
          (fst : yoneda.obj V ⟶ F.functorOfPoints) (snd : V ⟶ U),
          IsPullback fst (yoneda.map snd) f ξ → AlgebraicGeometry.IsOpenImmersion snd.left := sorry

/-- The identity morphism of an algebraic space is an open immersion. -/
instance IsOpenImmersion.id {S : Scheme.{u}} {F : AlgebraicSpace S} :
    IsOpenImmersion (𝟙 F) := sorry

/-- An open immersion of algebraic spaces is an immersion. -/
instance IsImmersion.ofIsOpenImmersion {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {f : F ⟶ G} [IsOpenImmersion f] : IsImmersion f := sorry

/-- A closed immersion of algebraic spaces is an immersion. -/
instance IsImmersion.ofIsClosedImmersion {S : Scheme.{u}} {F G : AlgebraicSpace S}
    {f : F ⟶ G} [IsClosedImmersion f] : IsImmersion f := sorry

end AlgebraicSpace

end AlgebraicGeometry

/-- An immersion of algebraic spaces is a monomorphism. -/
theorem AlgebraicGeometry.AlgebraicSpace.IsImmersion.mono
    {S : Scheme.{u}} {F G : AlgebraicGeometry.AlgebraicSpace S} {f : F ⟶ G}
    [AlgebraicGeometry.AlgebraicSpace.IsImmersion f] : Mono f := sorry

/-- An immersion of algebraic spaces is a separated morphism. -/
theorem AlgebraicGeometry.AlgebraicSpace.IsImmersion.separated
    {S : Scheme.{u}} {F G : AlgebraicGeometry.AlgebraicSpace S} {f : F ⟶ G}
    [AlgebraicGeometry.AlgebraicSpace.IsImmersion f] :
    AlgebraicGeometry.AlgebraicSpace.Separated f := sorry

attribute [instance] AlgebraicGeometry.AlgebraicSpace.IsImmersion.mono
  AlgebraicGeometry.AlgebraicSpace.IsImmersion.separated

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- If `g` is a monomorphism of algebraic spaces and `f ≫ g` has a relative scheme morphism
property `P`, then `f` has the same relative property. -/
theorem over_presheaf_of_comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    {P : MorphismProperty Scheme.{u}} (f : F ⟶ G) (g : G ⟶ H) [Mono g]
    (hfg : (over P).presheaf (f ≫ g)) : (over P).presheaf f := sorry

namespace IsImmersion

/-- If two immersions into an algebraic space factor as `j ≫ i₂ = i₁`, then `j` is
an immersion. -/
theorem of_comp {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂) [IsImmersion i₁] [IsImmersion i₂]
    (h : j ≫ i₂ = i₁) : IsImmersion j := sorry

end IsImmersion

namespace IsClosedImmersion

/-- If two closed immersions into an algebraic space factor as `j ≫ i₂ = i₁`, then `j` is
a closed immersion. -/
theorem of_comp {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (h : j ≫ i₂ = i₁) :
    IsClosedImmersion j := sorry

end IsClosedImmersion

namespace IsOpenImmersion

/-- If two open immersions into an algebraic space factor as `j ≫ i₂ = i₁`, then `j` is
an open immersion. -/
theorem of_comp {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (h : j ≫ i₂ = i₁) : IsOpenImmersion j := sorry

end IsOpenImmersion

end AlgebraicSpace

end AlgebraicGeometry
