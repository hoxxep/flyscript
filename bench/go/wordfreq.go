// Word frequencies: text built from a vocabulary, split into words, counted in a hash map, and
// the most frequent shown; strings, hashing and sorting.
package main
import ("fmt"; "os"; "sort"; "strconv"; "strings")
func main() {
	n := 1000; if len(os.Args) > 1 { n, _ = strconv.Atoi(os.Args[1]) }
	var b strings.Builder
	seed := uint64(42)
	for i := 0; i < n; i++ {
		seed = seed*6364136223846793005 + 1442695040888963407
		if i > 0 { b.WriteByte(' ') }
		b.WriteByte('w'); b.WriteString(strconv.FormatUint((seed>>33)%20000, 10))
	}
	counts := map[string]uint32{}
	for _, w := range strings.Fields(b.String()) { counts[w]++ }
	fmt.Printf("%d distinct words\n", len(counts))
	type kv struct{ k string; v uint32 }
	all := make([]kv, 0, len(counts))
	for k, v := range counts { all = append(all, kv{k, v}) }
	sort.Slice(all, func(i, j int) bool { if all[i].v != all[j].v { return all[i].v > all[j].v }; return all[i].k < all[j].k })
	for _, e := range all[:10] { fmt.Printf("%s %d\n", e.k, e.v) }
}
