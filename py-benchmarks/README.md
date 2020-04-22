First, let's create environment and install `lxml` (https://lxml.de/):

```
virtualenv -p /usr/bin/python3.8 py
source py/bin/activate
pip install lxml
pip install memory_profiler
```

Then we can run speed benchmark:

```
python bench-speed.py
```

And speed benchmark:

```
python -m memory_profiler bench-memory.py
```

