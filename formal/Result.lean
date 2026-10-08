import NormalizedBounds
import FiniteResult
import IntervalResult

/-!
Tuza's inequality for every finite split graph with at most two active
outside-neighborhood types. The numerical certificates are closed theorems.
OpenAI Codex (GPT-6 Astra).
-/
namespace TuzaTwoTypes
open Finset TuzaGraphCompression TuzaCoverCompression TuzaFinalClassification

/-- An active outside-neighborhood contains at least two core vertices. -/
noncomputable abbrev activeTypes := @TuzaFinalClassification.activeTypes

/-- Triangle edge-cover number is at most twice triangle-packing number. -/
theorem tuza_of_two_active_types {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : Finset V) (hK : G.IsClique K)
    (hI : ∀ a ∉ K, ∀ b ∉ K, ¬G.Adj a b)
    (htypes : (activeTypes G K).card ≤ 2) :
    coverNumber G ≤ 2 * packingNumber G := by
  exact TuzaFinalClassification.split_graph_two_active_types
    TuzaFiniteData.fallback TuzaFiniteData.all_checked TuzaIntervalData.all_checked
    G K hK hI htypes

#print axioms tuza_of_two_active_types
#check tuza_of_two_active_types
end TuzaTwoTypes
