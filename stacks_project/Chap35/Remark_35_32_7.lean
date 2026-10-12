/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Unramified
import StacksCheckRecall

open CategoryTheory

universe u

/- Remark 35.32.7 (1): flatness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Flat.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Flat : MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (2): local finite presentation is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (3): local finite type is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (4): universal openness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.UniversallyOpen.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.UniversallyOpen :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (5): syntomicity is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Syntomic.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Syntomic : MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (6): smoothness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Smooth.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Smooth : MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (7): étaleness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Etale.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Etale : MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (8): local quasi-finiteness in the finite-type sense is étale local on the
source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFiniteIsEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (9): unramifiedness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.Unramified.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.Unramified : MorphismProperty AlgebraicGeometry.Scheme.{u}))

/- Remark 35.32.7 (10): G-unramifiedness is étale local on the source and target. -/
@[stacks 04R3] #check
  (AlgebraicGeometry.GUnramified.isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.GUnramified : MorphismProperty AlgebraicGeometry.Scheme.{u}))
