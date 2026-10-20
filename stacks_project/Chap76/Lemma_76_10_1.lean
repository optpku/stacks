module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Properties
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 76.10.1 (1): affine morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.affine_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.Affine g.left ↔
      AlgebraicGeometry.AlgebraicSpace.Affine g.right)

/- Lemma 76.10.1 (2): surjective morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.surjective_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.Surjective g.left ↔
      AlgebraicGeometry.AlgebraicSpace.Surjective g.right)

/- Lemma 76.10.1 (3): quasi-compact morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.quasiCompact_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.QuasiCompact g.left ↔
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact g.right)

/- Lemma 76.10.1 (4): universally closed morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyClosed_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.UniversallyClosed g.left ↔
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed g.right)

/- Lemma 76.10.1 (5): integral morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.isIntegralHom_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.IsIntegralHom g.left ↔
      AlgebraicGeometry.AlgebraicSpace.IsIntegralHom g.right)

/- Lemma 76.10.1 (6): separated morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.separated_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.Separated g.left ↔
      AlgebraicGeometry.AlgebraicSpace.Separated g.right)

/- Lemma 76.10.1 (6): quasi-separated morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.quasiSeparated_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.QuasiSeparated g.left ↔
      AlgebraicGeometry.AlgebraicSpace.QuasiSeparated g.right)

/- Lemma 76.10.1 (7): universally injective morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyInjective_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.UniversallyInjective g.left ↔
      AlgebraicGeometry.AlgebraicSpace.UniversallyInjective g.right)

/- Lemma 76.10.1 (8): universally open morphisms are invariant under a morphism of
thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.universallyOpen_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    AlgebraicGeometry.AlgebraicSpace.UniversallyOpen g.left ↔
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen g.right)

/- Lemma 76.10.1 (9): representable morphisms are invariant under a morphism of thickenings. -/
@[stacks 09ZY] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.Hom.relativelyRepresentable_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {T U : AlgebraicGeometry.AlgebraicSpace.Thickening S}
    (g : T ⟶ U),
    yoneda.relativelyRepresentable g.left ↔ yoneda.relativelyRepresentable g.right)
