go build

# ln -sf "$(pwd)/linescript4" /usr/local/bin/linescript4
rm /usr/local/linescript4
ln -s "$(pwd)" /usr/local/linescript4

rm /usr/local/bin/linescript4
cp "$(pwd)/linescript4" /usr/local/bin/linescript4

echo "#closeme"
