module

public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Cofibered

/-!
# Fibrewise isomorphism classes after residue-field change

The fibre comparison identifies isomorphism classes of
`residueChangeOver p` over `B` with those of `p` over `B ×_l k`.
-/

@[expose] public section

open CategoryTheory Functor

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

noncomputable section

namespace residueChangeOver

/-- The class map induced by the fibre embedding is a left inverse to the
class map induced by the forward fibre comparison. -/
theorem isoClassMaps_leftInverse [IsFibered.InGroupoids p.op]
    (B : ArtinianLocalAlgCat Λ l) :
    Function.LeftInverse (fiberMk Λ k l p B).isoClassesMap
      (fiberFwd Λ k l p B).isoClassesMap :=
  sorry

/-- The class map induced by the fibre embedding is a right inverse to the
class map induced by the forward fibre comparison. -/
theorem isoClassMaps_rightInverse [IsFibered.InGroupoids p.op]
    (B : ArtinianLocalAlgCat Λ l) :
    Function.RightInverse (fiberMk Λ k l p B).isoClassesMap
      (fiberFwd Λ k l p B).isoClassesMap :=
  sorry

/-- Pointwise identification of fibrewise isomorphism classes:
`fiberIsoClassFunctor (residueChangeOver p)` at `B` with
`fiberIsoClassFunctor p` at `(residueChangeFunctor Λ k l).obj B`. -/
def isoClassEquiv [IsFibered.InGroupoids p.op] (B : ArtinianLocalAlgCat Λ l) :
    isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B)) ≃
      isomorphismClasses.obj
        (Cat.of (p.Fiber ((residueChangeFunctor Λ k l).obj B))) where
  toFun := (fiberFwd Λ k l p B).isoClassesMap
  invFun := (fiberMk Λ k l p B).isoClassesMap
  left_inv := isoClassMaps_leftInverse Λ k l p B
  right_inv := isoClassMaps_rightInverse Λ k l p B

/-- The forward map of `isoClassEquiv` is `isoClassesMap` of `fiberFwd`. -/
theorem isoClassEquiv_apply [IsFibered.InGroupoids p.op]
    (B : ArtinianLocalAlgCat Λ l) (x : (residueChangeOver Λ k l p).Fiber B) :
    isoClassEquiv Λ k l p B (Quotient.mk'' x) =
      (fiberFwd Λ k l p B).isoClassesMap (Quotient.mk'' x) :=
  sorry

/-- The inverse map of `isoClassEquiv` is `isoClassesMap` of `fiberMk`. -/
theorem isoClassEquiv_symm_apply [IsFibered.InGroupoids p.op]
    (B : ArtinianLocalAlgCat Λ l)
    (y : p.Fiber ((residueChangeFunctor Λ k l).obj B)) :
    (isoClassEquiv Λ k l p B).symm (Quotient.mk'' y) =
      (fiberMk Λ k l p B).isoClassesMap (Quotient.mk'' y) :=
  sorry

/-- `isoClassEquiv` intertwines `fiberIsoClassFunctor (residueChangeOver p)` with
`fiberIsoClassFunctor p` after `residueChangeFunctor`. -/
theorem isoClassEquiv_natural [IsFibered.InGroupoids p.op]
    {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B')
    (x : isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B))) :
    isoClassEquiv Λ k l p B'
        ((fiberIsoClassFunctor (residueChangeOver Λ k l p)).map f x) =
      (fiberIsoClassFunctor p).map ((residueChangeFunctor Λ k l).map f)
        (isoClassEquiv Λ k l p B x) :=
  sorry

end residueChangeOver

end

end ArtinianLocalAlgCat
