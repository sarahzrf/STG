%big = type [2000000000 x i8]
@mem = global %big zeroinitializer
@allocptr = global i8* getelementptr(%big, %big* @mem, i32 0, i32 0)

define i8* @calloc(i64 %a, i64 %b) {
  %size = mul i64 %a, %b
  %cur = load i8*, i8** @allocptr
  %new = getelementptr i8, i8* %cur, i64 %size
  store i8* %new, i8** @allocptr
  ret i8* %cur
}

