module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry

universe u v

/- Definition 76.13.1 (1): Let `S` be a scheme. Let `a : F ⟶ G` be a transformation
of functors `F, G : (Over S)ᵒᵖ ⥤ Type`. We say `a` is formally smooth if every
solid commutative square against an affine closed immersion `i : T ⟶ T'` defined
by a square-zero ideal admits a dotted lift `T' ⟶ F`. -/
@[stacks 049S]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)

/- Definition 76.13.1 (2): Let `S` be a scheme. Let `a : F ⟶ G` be a transformation
of functors `F, G : (Over S)ᵒᵖ ⥤ Type`. We say `a` is formally étale if every
solid commutative square against an affine closed immersion `i : T ⟶ T'` defined
by a square-zero ideal admits a unique dotted lift `T' ⟶ F`. -/
@[stacks 049S]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)

/- Definition 76.13.1 (3): Let `S` be a scheme. Let `a : F ⟶ G` be a transformation
of functors `F, G : (Over S)ᵒᵖ ⥤ Type`. We say `a` is formally unramified if every
solid commutative square against an affine closed immersion `i : T ⟶ T'` defined
by a square-zero ideal admits at most one dotted lift `T' ⟶ F`. -/
@[stacks 049S]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified :
    {S : Scheme.{u}} → {F G : (Over S)ᵒᵖ ⥤ Type v} → (F ⟶ G) → Prop)
