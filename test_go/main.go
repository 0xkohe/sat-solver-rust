package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"
)

func main() {
	scanner := bufio.NewScanner(os.Stdin)

	//skip first line
	scanner.Scan()
	fs := []string{}
	for scanner.Scan() {
		line := scanner.Text()
		fs = strings.Fields(line)
		// 読み取った行をそのまま出力
		// fmt.Println("Read from stdin:", line)
	}
	// エラーチェック
	if err := scanner.Err(); err != nil {
		fmt.Fprintln(os.Stderr, "Error reading from stdin:", err)
	}

	t := map[int]struct{}{}
	for _, v := range fs {
		if v == "v" {
			continue
		}

		vv, _ := strconv.Atoi(v)
		t[vv] = struct{}{}
	}

	for i := 100; i <= 900; i += 100 {
		for j := 10; j <= 90; j += 10 {
			for k := 1; k <= 9; k++ {
				if _, ok := t[i+j+k]; ok {
					fmt.Printf("%d ", k)
					break
				}
			}
		}
		fmt.Println()
	}

}
