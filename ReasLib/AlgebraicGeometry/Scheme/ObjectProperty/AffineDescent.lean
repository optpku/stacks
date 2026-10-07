module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AffineScheme.StandardMorphisms
public import ReasLib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.StandardRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ObjectProperty

variable (P : CategoryTheory.ObjectProperty Scheme.{u})

/-- A Zariski-local property that ascends along flat morphisms of affine schemes and
descends along surjective flat morphisms of affine schemes is fpqc-local. -/
instance fpqcLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.fpqcPrecoverage := sorry

/-- A Zariski-local property that ascends along flat, locally finitely presented morphisms
of affine schemes and descends along their surjective members is fppf-local. -/
instance fppfLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective) : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.fppfPrecoverage := sorry

/-- A Zariski-local property that ascends along étale morphisms of affine schemes and
descends along surjective étale morphisms of affine schemes is étale-local. -/
instance etaleLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Etale ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.etalePrecoverage := sorry

/-- A Zariski-local property that ascends along smooth morphisms of affine schemes and
descends along surjective smooth morphisms of affine schemes is smooth-local. -/
instance smoothLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Smooth ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSmoothPrecoverage := sorry

/-- A Zariski-local property that ascends along syntomic morphisms of affine schemes and
descends along surjective syntomic morphisms of affine schemes is syntomic-local. -/
instance syntomicLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (MorphismProperty.inverseImage
        ((@Syntomic ⊓ @Surjective) : MorphismProperty Scheme.{u}) AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local property that ascends along smooth morphisms of affine schemes and
descends along surjective standard smooth morphisms of affine schemes is smooth-local. -/
instance standardSmoothLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSmooth ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSmoothPrecoverage := sorry

/-- A Zariski-local property that ascends along syntomic morphisms of affine schemes and
descends along surjective standard syntomic morphisms of affine schemes is syntomic-local. -/
instance standardSyntomicLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardSyntomic ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.bigSyntomicPrecoverage := sorry

/-- A Zariski-local property that ascends along étale morphisms of affine schemes and
descends along surjective standard étale morphisms of affine schemes is étale-local. -/
instance standardEtaleLocalOfZariskiLocal
    [P.IsLocal Scheme.zariskiPrecoverage]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromTarget
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        AffineScheme.forgetToScheme)]
    [(P.inverseImage AffineScheme.forgetToScheme).InheritedFromSource
      (AffineScheme.standardEtale ⊓
        MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)] :
    P.IsLocal Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.ObjectProperty
