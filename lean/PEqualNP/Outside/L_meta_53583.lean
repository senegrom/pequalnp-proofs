import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_53583 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903036 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  let C : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [6, 16]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
