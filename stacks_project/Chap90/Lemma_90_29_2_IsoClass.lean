/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.IsoClass
import StacksCheckRecall

/-!
# Fibrewise isomorphism classes after residue-field change
-/

@[expose] public section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

section IsoClass

variable [IsFibered.InGroupoids p.op]

/- Lemma 90.29.2 (1): Fibrewise isomorphism classes commute naturally with
residue-field change. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B)) ≃
      isomorphismClasses.obj (Cat.of (p.Fiber ((residueChangeFunctor Λ k l).obj B))))

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv_natural Λ k l p :
  ∀ {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B')
    (x : isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B))),
    ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B'
        ((fiberIsoClassFunctor (residueChangeOver Λ k l p)).map f x) =
      (fiberIsoClassFunctor p).map ((residueChangeFunctor Λ k l).map f)
        (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B x))

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassMaps_leftInverse Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    Function.LeftInverse (ArtinianLocalAlgCat.residueChangeOver.fiberMk Λ k l p B).isoClassesMap
      (ArtinianLocalAlgCat.residueChangeOver.fiberFwd Λ k l p B).isoClassesMap)

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassMaps_rightInverse Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    Function.RightInverse (ArtinianLocalAlgCat.residueChangeOver.fiberMk Λ k l p B).isoClassesMap
      (ArtinianLocalAlgCat.residueChangeOver.fiberFwd Λ k l p B).isoClassesMap)

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv_apply Λ k l p :
  ∀ (B : ArtinianLocalAlgCat Λ l) (x : (residueChangeOver Λ k l p).Fiber B),
    ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B (Quotient.mk'' x) =
      (ArtinianLocalAlgCat.residueChangeOver.fiberFwd Λ k l p B).isoClassesMap (Quotient.mk'' x))

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv_symm_apply Λ k l p :
  ∀ (B : ArtinianLocalAlgCat Λ l) (y : p.Fiber ((residueChangeFunctor Λ k l).obj B)),
    (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B).symm (Quotient.mk'' y) =
      (ArtinianLocalAlgCat.residueChangeOver.fiberMk Λ k l p B).isoClassesMap (Quotient.mk'' y))

end IsoClass
