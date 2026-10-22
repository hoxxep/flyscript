// fannkuch-redux: permutations of small arrays, flipped; integer work over arrays.
package main
import ("fmt"; "os"; "strconv")
func main() {
	n := 7; if len(os.Args) > 1 { n, _ = strconv.Atoi(os.Args[1]) }
	var perm, perm1, count [16]int
	maxFlips, checksum, r, permCount := 0, 0, n, 0
	for i := 0; i < n; i++ { perm1[i] = i }
	for {
		for ; r != 1; r-- { count[r-1] = r }
		perm = perm1
		flips := 0
		for k := perm[0]; k != 0; k = perm[0] {
			for i, j := 0, k; i < j; i, j = i+1, j-1 { perm[i], perm[j] = perm[j], perm[i] }
			flips++
		}
		if flips > maxFlips { maxFlips = flips }
		if permCount%2 == 0 { checksum += flips } else { checksum -= flips }
		for {
			if r == n { fmt.Printf("%d\nPfannkuchen(%d) = %d\n", checksum, n, maxFlips); return }
			p0 := perm1[0]
			for i := 0; i < r; i++ { perm1[i] = perm1[i+1] }
			perm1[r] = p0
			count[r]--
			if count[r] > 0 { break }
			r++
		}
		permCount++
	}
}
