module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Descent

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DescentData
open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- The concrete scheme descent datum. -/
#check (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.descentData :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2),
    DescentData (fun _ : PUnit.{1} ↦ Spec (CommRingCat.of k')) (fun _ ↦ groundCover k k'))
